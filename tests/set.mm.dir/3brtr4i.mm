include "eqbrtri.mm"
include "breqtrri.mm"

theorem 3brtr4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume 3brtr4.1: |- A R B
  assume 3brtr4.2: |- C = A
  assume 3brtr4.3: |- D = B


  assert |- C R D

  proof
    cC
    cB
    cD
    cR
    cC
    cA
    cB
    cR
    3brtr4.2
    3brtr4.1
    eqbrtri
    3brtr4.3
    breqtrri
end
