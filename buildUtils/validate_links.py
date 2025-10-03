#!/usr/bin/env python3
"""
Link validation script for SBV project
Checks all HTTP/HTTPS links in markdown and Haskell files for validity
"""

import re
import urllib.request
import urllib.error
import ssl
import sys
import os
import time
import random
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import defaultdict

def extract_links_from_file(filepath):
    """Extract all HTTP/HTTPS links from a file with line numbers"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        # Pattern to match HTTP/HTTPS URLs
        url_patterns = [
            r'https?://[^\s\)\]\>\'"]+',  # Plain URLs
            r'\[([^\]]*)\]\((https?://[^\)]+)\)',  # Markdown links
            r'<(https?://[^>]+)>',  # URLs in angle brackets
        ]

        links = []
        for line_num, line in enumerate(lines, 1):
            for pattern in url_patterns:
                matches = re.finditer(pattern, line)
                for match in matches:
                    if pattern.startswith(r'\['):
                        # For markdown links, extract the URL (group 2)
                        url = match.group(2)
                        text = match.group(1)
                    elif pattern.startswith(r'<'):
                        # For angle bracket URLs, extract group 1
                        url = match.group(1)
                        text = url
                    else:
                        # For plain URLs
                        url = match.group(0)
                        text = url

                    # Clean up the URL (remove trailing punctuation and quotes)
                    url = url.rstrip('.,;:!?)\'"')
                    links.append((url, text, line_num, match.start()))

        return links
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
        return []

def check_link(url, timeout=15, max_retries=3):
    """Check if a URL is accessible with retry logic"""
    # List of user agents to rotate through
    user_agents = [
        'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.1 Safari/605.1.15',
        'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
    ]

    for attempt in range(max_retries):
        try:
            # Add random delay to avoid rate limiting
            if attempt > 0:
                time.sleep(random.uniform(1, 3))

            # Create a context that doesn't verify SSL certificates
            ctx = ssl.create_default_context()
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE

            # Use different user agent for each retry
            user_agent = user_agents[attempt % len(user_agents)]

            # Create request with headers to appear more like a real browser
            req = urllib.request.Request(
                url,
                headers={
                    'User-Agent': user_agent,
                    'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
                    'Accept-Language': 'en-US,en;q=0.5',
                    'Accept-Encoding': 'gzip, deflate',
                    'DNT': '1',
                    'Connection': 'keep-alive',
                    'Upgrade-Insecure-Requests': '1',
                }
            )

            # Try to open the URL
            with urllib.request.urlopen(req, timeout=timeout, context=ctx) as response:
                status_code = response.getcode()
                if 200 <= status_code < 400:
                    return True, status_code, None
                else:
                    # Don't retry for client errors (400-499)
                    if 400 <= status_code < 500:
                        return False, status_code, f"HTTP {status_code}"
                    # Continue to retry for server errors (500+)

        except urllib.error.HTTPError as e:
            # Don't retry for certain client errors
            if e.code in [404, 410]:  # Not found, gone
                return False, e.code, f"HTTP {e.code}: {e.reason}"
            elif e.code == 403 and attempt < max_retries - 1:
                # Retry 403 errors as they might be rate limiting
                continue
            else:
                if attempt == max_retries - 1:
                    return False, e.code, f"HTTP {e.code}: {e.reason} (after {max_retries} attempts)"
        except urllib.error.URLError as e:
            if attempt == max_retries - 1:
                return False, None, f"URL Error: {e.reason} (after {max_retries} attempts)"
        except Exception as e:
            if attempt == max_retries - 1:
                return False, None, f"Error: {str(e)} (after {max_retries} attempts)"

    return False, None, f"Failed after {max_retries} attempts"

def validate_links_in_files(filepaths, max_workers=3, delay_between_requests=0.5):
    """Validate all links found in the given files"""
    all_links = defaultdict(list)  # url -> [(filepath, text, line_num, position), ...]

    # Extract all links from all files
    for filepath in filepaths:
        links = extract_links_from_file(filepath)
        for url, text, line_num, position in links:
            all_links[url].append((filepath, text, line_num, position))

    print(f"Found {len(all_links)} unique URLs to check")

    if not all_links:
        print("No links found to validate")
        return all_links, {}

    # Check links with reduced concurrency and delays
    results = {}
    urls = list(all_links.keys())
    total_urls = len(urls)

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        # Submit tasks with staggered delays
        futures = {}
        for i, url in enumerate(urls):
            if i > 0:
                time.sleep(delay_between_requests)
            future = executor.submit(check_link, url)
            futures[future] = url

            # Show which URL we're about to check with progress (overwrite previous line)
            short_url = url[:50] + "..." if len(url) > 50 else url
            print(f"\rChecking ({i+1}/{total_urls}): {short_url:<55}", end="", flush=True)

        completed = 0
        valid_count = 0
        invalid_count = 0

        for future in as_completed(futures):
            url = futures[future]
            try:
                is_valid, status_code, error = future.result()
                results[url] = (is_valid, status_code, error)
                completed += 1

                if is_valid:
                    valid_count += 1
                    # Just clear the checking line for valid URLs, don't print anything
                    print(f"\r{' ' * 80}", end="", flush=True)
                else:
                    invalid_count += 1
                    # Print broken link immediately with locations
                    print(f"\r✗ BROKEN: {url}")
                    if error:
                        print(f"  Error: {error}")

                    # Show locations with line numbers (limit to first 3)
                    locations = all_links[url][:3]
                    for filepath, text, line_num, position in locations:
                        print(f"  {filepath}:{line_num}")

                    if len(all_links[url]) > 3:
                        print(f"  ... and {len(all_links[url]) - 3} more locations")

                # Add small delay between processing results
                time.sleep(0.1)

            except Exception as e:
                results[url] = (False, None, f"Exception: {str(e)}")
                invalid_count += 1
                completed += 1

    # Clear any remaining checking line
    print(f"\r{' ' * 80}", end="", flush=True)

    return all_links, results, valid_count, invalid_count

def filter_files_by_priority(target_files, priority_only=False):
    """Filter files by priority (docs first, then key source files)"""
    if not priority_only:
        return target_files

    priority_files = []

    # High priority: documentation files and special files
    for f in target_files:
        if any(doc in f.lower() for doc in ['readme', 'changes', 'smt', 'doc']):
            priority_files.append(f)
        # Include special files like LICENSE, COPYRIGHT, INSTALL
        elif any(special in f.upper() for special in ['LICENSE', 'COPYRIGHT', 'INSTALL', 'COPYING', 'NOTICE', 'AUTHORS']):
            priority_files.append(f)

    # Medium priority: main library files
    for f in target_files:
        if f.startswith('./Data/SBV.hs') or f.startswith('./Data/SBV/'):
            if len(f.split('/')) <= 3:  # Only top-level files
                priority_files.append(f)

    return list(set(priority_files))  # Remove duplicates

def main():
    parser = argparse.ArgumentParser(description='Validate HTTP/HTTPS links in SBV project files')
    parser.add_argument('--priority-only', action='store_true',
                       help='Only check high-priority files (docs and main library files)')
    parser.add_argument('--max-workers', type=int, default=3,
                       help='Maximum number of concurrent workers (default: 3)')
    parser.add_argument('--delay', type=float, default=0.5,
                       help='Delay between requests in seconds (default: 0.5)')
    parser.add_argument('--file-types', nargs='+', default=['.md', '.hs'],
                       help='File extensions to check (default: .md .hs)')

    args = parser.parse_args()

    # Find all target files in the project
    target_files = []

    # Special files to always include (LICENSE, COPYRIGHT, INSTALL, etc.)
    special_files = ['COPYRIGHT', 'INSTALL', 'LICENSE', 'COPYING', 'NOTICE', 'AUTHORS']

    for root, dirs, files in os.walk('.'):
        # Skip hidden directories and build directories
        dirs[:] = [d for d in dirs if not d.startswith('.') and d != 'dist-newstyle']

        for file in files:
            # Include files with specified extensions
            if any(file.endswith(ext) for ext in args.file_types):
                target_files.append(os.path.join(root, file))
            # Include special files (LICENSE, COPYRIGHT, etc.) regardless of extension
            elif file.upper() in [sf.upper() for sf in special_files]:
                target_files.append(os.path.join(root, file))

    if not target_files:
        print(f"No files found with extensions: {args.file_types}")
        return

    # Filter by priority if requested
    if args.priority_only:
        target_files = filter_files_by_priority(target_files, priority_only=True)
        print(f"Priority mode: checking {len(target_files)} high-priority files")

    # Count files by type (including special files)
    file_counts = {}
    special_count = 0
    for ext in args.file_types:
        count = sum(1 for f in target_files if f.endswith(ext))
        if count > 0:
            file_counts[ext] = count

    # Count special files (LICENSE, COPYRIGHT, etc.)
    special_files = ['COPYRIGHT', 'INSTALL', 'LICENSE', 'COPYING', 'NOTICE', 'AUTHORS']
    for f in target_files:
        filename = os.path.basename(f).upper()
        if filename in [sf.upper() for sf in special_files]:
            special_count += 1

    # Create display string
    counts_display = []
    for ext, count in file_counts.items():
        counts_display.append(f'{count} {ext}')
    if special_count > 0:
        counts_display.append(f'{special_count} special')

    print(f"Found {len(target_files)} files: {', '.join(counts_display)}")

    # Validate links
    all_links, results, valid_count, invalid_count = validate_links_in_files(target_files,
                                               max_workers=args.max_workers,
                                               delay_between_requests=args.delay)

    if not results:
        return

    # Simple one-line summary
    total_links = valid_count + invalid_count
    print(f"\rSUMMARY: {total_links} links checked - {valid_count} valid, {invalid_count} broken")

    if invalid_count > 0:
        if not args.priority_only:
            print("Consider using --priority-only to focus on documentation files first.")
        return 1
    else:
        return 0

if __name__ == "__main__":
    sys.exit(main())