A Haskell implementation of Solomonoff Induction using probabilistic oracle
machines.

This was mostly implemented to verify that the implementation type-checks.

It won't work properly unless you implement a reflective oracle (which is only
slightly harder than implementing a halting oracle), but you can implement
various "dumb" oracles and verify that various parts of the code work.
