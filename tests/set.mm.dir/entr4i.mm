include "ensymi.mm"
include "entri.mm"

theorem entr4i
  let cA: class A
  let cB: class B
  let cC: class C
  assume entr4i.1: |- A ~~ B
  assume entr4i.2: |- C ~~ B


  assert |- A ~~ C

  proof
    cA
    cB
    cC
    entr4i.1
    cC
    cB
    entr4i.2
    ensymi
    entri
end
