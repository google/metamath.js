include "ensymi.mm"
include "entri.mm"

theorem entr3i
  let cA: class A
  let cB: class B
  let cC: class C
  assume entr3i.1: |- A ~~ B
  assume entr3i.2: |- A ~~ C


  assert |- B ~~ C

  proof
    cB
    cA
    cC
    cA
    cB
    entr3i.1
    ensymi
    entr3i.2
    entri
end
