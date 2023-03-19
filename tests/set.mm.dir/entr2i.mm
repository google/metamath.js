include "entri.mm"
include "ensymi.mm"

theorem entr2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume entr2i.1: |- A ~~ B
  assume entr2i.2: |- B ~~ C


  assert |- C ~~ A

  proof
    cA
    cC
    cA
    cB
    cC
    entr2i.1
    entr2i.2
    entri
    ensymi
end
