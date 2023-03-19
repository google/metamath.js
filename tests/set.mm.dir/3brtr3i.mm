include "eqbrtrri.mm"
include "breqtri.mm"

theorem 3brtr3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume 3brtr3.1: |- A R B
  assume 3brtr3.2: |- A = C
  assume 3brtr3.3: |- B = D


  assert |- C R D

  proof
    cC
    cB
    cD
    cR
    cA
    cC
    cB
    cR
    3brtr3.2
    3brtr3.1
    eqbrtrri
    3brtr3.3
    breqtri
end
