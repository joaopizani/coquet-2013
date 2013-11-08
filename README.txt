	  **************************************************
	  * Coquet: A Coq library for verifying hardware.  *
	  **************************************************


This work is described in a paper submitted to CPP (2011). 
Author: Thomas Braibant, thomas.braibant@gmail.com
Date: 06/2011

Abstract
========

  We propose a new library to model and verify hardware circuits in
  the Coq proof assistant.

  This library allows one to easily build circuits by following the
  usual pen-and-paper diagrams. We define a deep-embedding: we use a
  (dependently typed) data-type that models the architecture of
  circuits, and a meaning function.

  We propose tactics that ease the reasoning about the behavior of the
  circuits, and we demonstrate that our approach is practicable by
  proving the correctness of various circuits: a text-book divide and
  conquer adder of parametric size, some higher-order combinators of
  circuits, and some sequential circuits: a buffer, and a register.

Description of the files
========================

- Axioms.v: the axioms we use (FunctionalExtensionality and proof irrelevance) 

- Common.v: some definitions we re-use through the development

- EqT.v: types with a boolean equality

- Finite.v: finite types (types with a duplicate free enumeration)

- Sumn.v: n-ary disjoint sums

- Vector.v: length-indexed n-uples. 

- Word.v: n-bit integers (non-fixed size) 

- Data.v : operations on finite functions

- Reify.v: isomorphisms between types

- Base.v: the definition of the type of the circuits, and the meaning relation.

- Count.v Simulation.v Netlist.v Delay.v Lifting.v: some
  interpretations of the circuits (gate-count, simulation, pretty
  printing to netlists, delay, lifting the menaing to streams)

- Combinators.v: high-level combinators of circuits. 

- Examples/Doors.v: Basic doors, starting from NOR (goes to the full-adder)
  
- Examples/Muxer.v: n-bit multiplexers

- Examples/Ripple.v: ripple carry adder

- Examples/DC.v : divide and conquer adder

- Examples/FIFO.v : fifo-buffer

- Examples/Register.v : one bit memory element. 

- Examples/Interpretations.v: use several interpretations to compute the gate delay, the gate-count and the netlist of various circuits.

COMPILATION
===========

- Just do [make all] in the root directory (may take some time)

- [make test] compiles the Examples/Interpreations.v file (may takes some time)

- requires coq 8.3 pl2 

