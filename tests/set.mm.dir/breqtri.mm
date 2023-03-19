include "wbr.mm"
include "breq2i.mm"
include "mpbi.mm"

theorem breqtri
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breqtr.1: |- A R B
  assume breqtr.2: |- B = C


  assert |- A R C

  proof
    cA
    cB
    cR
    wbr
    cA
    cC
    cR
    wbr
    breqtr.1
    cB
    cC
    cA
    cR
    breqtr.2
    breq2i
    mpbi
end
