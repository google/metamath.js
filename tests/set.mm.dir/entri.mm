include "cen.mm"
include "wbr.mm"
include "entr.mm"
include "mp2an.mm"

theorem entri
  let cA: class A
  let cB: class B
  let cC: class C
  assume entri.1: |- A ~~ B
  assume entri.2: |- B ~~ C


  assert |- A ~~ C

  proof
    cA
    cB
    cen
    wbr
    cB
    cC
    cen
    wbr
    cA
    cC
    cen
    wbr
    entri.1
    entri.2
    cA
    cB
    cC
    entr
    mp2an
end
