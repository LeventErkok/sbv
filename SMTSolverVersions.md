SBV has been tested with the following versions of the SMT solvers. While we strive to make sure
it works with latest releases of each of these tools, newer versions can exhibit issues. Please
report any issues you might see with newer releases.

  * ABC:
      * http://github.com/berkeley-abc/abc
      * Version as downloaded from the above site on Apr 25, 2022
  * Boolector:
      * https://boolector.github.io
      * Version 3.2.2
  * Bitwuzla:
      * https://bitwuzla.github.io
      * Version 1.0-prerelease
  * CVC4:
      * https://github.com/CVC4/CVC4
      * Version installed via `brew tap cvc4/cvc4; brew rm cvc4; brew install cvc4/cvc4/cvc4 --HEAD`
        on Jul 27, 2020.
  * CVC5:
      * https://github.com/cvc5/cvc5
      * Version 1.0.5, downloaded compiled from GitHub repo above on Mar 13th, 2023.
  * dReal:
      * http://dreal.github.io/
      * Version installed via `brew tap dreal/dreal; brew rm dreal; brew install dreal --HEAD`
        on Jul 25, 2020.
  * MathSAT:
      * http://mathsat.fbk.eu/
      * Version 5.6.5
  * Yices:
      * http://github.com/SRI-CSL/yices2
      * Version 2.6.2 as downloaded from the above site on Apr 7, 2020
  * Z3:
      * http://github.com/Z3Prover/z3
      * Version as downloaded from the above site on Oct 29th, 2023
      * SBV typically relies on latest features of z3, so compiling directly
        from the sources is recommended. If that's not possible, you should
        always use their latest release.
