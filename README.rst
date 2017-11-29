Set Replication Demo
====================

This is a demo project to show the full process of developing an end-to-end
mechanically proved distributed system. It is inspired by the ``Count.v``
example in Verdi project, though the problem is redesigned and proof is
rewritten.

The project achieves a simple primary-backup-style replication. Each node from
either primary or backup maintains a set of natural numbers as its internal
state. There are only two external events to the system: add a new number
(maybe a duplicate of existing ones), or query the current state of the
primary.  The goal and its proof of the system is to ensure at any global state
reachable from the initial state, namely, at any possible moment, the set
maintained by the backup is always a subset of the primary. The networking is
modeled to be fully asynchronous, but still reliable (no packet loss or
duplication).

The Coq file first captures the network semantics (borrow from ``Count.v``
example), then defines the protocol using monadic handlers. Then, lists are
used to model the mathematical properties of sets, and a bunch of utility
lemmas are thus proved. Finally, the invariant is defined and proved which
leads to the proof of the safety theorem.

The proof is checked by Coq and automatically extracted to a Haskell source
code file ``SetReplicationCore.hs`` which is used as-is in the implementation.
The ``Main.hs`` is merely a wrapper which provides with the actual TCP
communication and keeps the state for each process. Types used by Coq are
converted by the helper functions (especially ``nat``, which should be
non-trivially converted to ``Int``). The incoming data are forwarded to handler
``processInput`` and ``processMsg`` so the generated Haskell code takes main
control of the program logic.

Files
-----
- set_replication.v -- the Coq source code
- SetReplicationCore.hs -- the extracted Haskell code
- demo/app/Main.hs -- the Haskell main program
- report/report.pdf -- the report
