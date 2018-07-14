.. SBV documentation master file, created by
   sphinx-quickstart on Sat Jul 14 13:03:10 2018.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

SBV: SMT Based Verification
===========================

The SBV library aims to seamlessly integrate SMT solvers with Haskell. The goal
is to express properties about Haskell programs and automatically prove them using
SMT solvers::

    $ ghci
    ghci> :m Data.SBV
    ghci> prove $ \x -> x `shiftL` 2 .== 4 * (x::SWord8)
    Q.E.D.
    ghci> prove $ \x -> x `shiftL` 2 .== 2 * (x::SWord8)
    Falsifiable. Counter-example:
      s0 = 32 :: Word8

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   introduction/introduction
   thanks/thanks

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
