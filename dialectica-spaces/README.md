Dialectica Spaces
-----------------

This is a formalization of dialectica spaces in the two flavors from
Valeria de Paiva's thesis.  The first flavor is DC over Sets and the
second is GC over sets.  We call the latter Dial over sets.

Each type of space requires the notion of a lineale. A lineale is
essentially a symmetric monoidal closed category in the category of
partially ordered sets. (or A lineale corresponds to the
poset-reflection of the notion of a monoidal closed category).

- Defined in [lineale.agda](lineale.agda)
- Theorems about lineales can be found in [lineale-thms.agda](lineale-thms.agda)
- Definitions of concrete lineales can be found in [concrete-lineales.agda](concrete-lineales.agda)

Finally, we have the two types of dialectica spaces:

- DC over sets can be found in [DCSets.agda](DCSets.agda)
- Dial over sets can be found in [DialSets.agda](DialSets.agda)

This formalization was developed and tested with Agda 2.4.2.4 and
depends on the [Augusta University Agda
Library](https://github.com/heades/AUGL).