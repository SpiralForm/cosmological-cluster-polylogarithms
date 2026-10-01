# Polylogarithms for cosmological wavefunctions

Wolfram Language code for expressing cosmological chain and loop wavefunctions in terms of quadrangular polylogarithms and related multiple polylogarithms. This repository contains the current PolyLogTools-free implementation and a selected set of core calculations.

The chain calculations accompany L. Ferro, T. Łukowski, L. Ren, M. Spradlin, A. Volovich, H.-C. Weng and Y.-Q. Zhang, *de Sitter Wavefunction from Quadrangular Polylogarithms: Chain Graphs*, [arXiv:2605.06542](https://arxiv.org/abs/2605.06542).

## Requirement

- [NumPolyLog](https://github.com/munuxi/Multiple-Polylogarithm)

## Packages

- `symbology.m` — generic multiple-polylogarithm and symbol operations.
- `orthoschemenew.m` — the active PolyLogTools-free implementation of the A-type and modified B-type constructions.

Install NumPolyLog separately, then load `symbology.m` and `orthoschemenew.m` in the listed order.

## Selected calculations

- `examples/chain/chain_anc_file.nb` — the principal ancillary chain calculation.
- `examples/loop/QLiB.m` — compact source for the modified B-type construction.
- `examples/loop/QLiB.nb` — explicit loop formulas and checks.
- `examples/loop/cluster_loop_new_toshare.nb` — the principal collaborator-facing loop calculation.

## Author

Lecheng Ren, with research results developed in the collaboration cited above.
