{-
layout: default
title : Relations module (The Agda Universal Algebra Library)
date : 2021-01-12
author: [agda-algebras development team][]
-}

-- Relation and Quotient Types
-- ===========================
--
-- This is the [UniversalAlgebra.Relations][] module of the [Agda Universal Algebra Library][].
--
-- In [Relations.Discrete][] we define types that represent *unary* and *binary relations*, which we refer to
-- as "discrete relations" to contrast them with the ("continuous") *general* and *dependent relations* that
-- we introduce in [Relations.Continuous][]. We call the latter "continuous relations" because they can have
-- arbitrary arity (general relations) and they can be defined over arbitrary families of types (dependent
-- relations).


{-# OPTIONS --without-K --exact-split --safe #-}

module Relations where

open import Relations.Discrete public
open import Relations.Continuous public
open import Relations.Quotients public
open import Relations.Truncation public
open import Relations.Extensionality public

----------------------------

-- [agda-algebras development team]: https://github.com/ualib/agda-algebras#the-agda-algebras-development-team
