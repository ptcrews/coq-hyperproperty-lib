# Coq Hyperproperty Library

This repo contains a hyperproperty library written in Coq.

As of 2023-12-12, work on this library is still ongoing, and we expect
significant changes to the interface to occur.

## Library Layout

This library consists of core hyperproperty definitions and proofs
(`Hyperproperties.v`), two example hyperproperties and proofs
(`GuaranteedService.v` and `ObservationalDeterminism.v`), and an example system
(`CrashSystem.v`).

## Build Instructions

This code was built with Coq version 8.17.1. To build this library, clone the
repo and run:

```
make
```

This should verify all proofs in all files.

## Known Issues

A small number of lemmas outside of the `Hyperproperties.v` file are not yet
completed. Note that all proofs inside the `Hyperproperties.v` file are
complete.

This library currently uses classical logic and assumes the excluded middle for
some proofs. Future work aims to remove this dependency.
