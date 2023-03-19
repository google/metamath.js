include "cvv.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "numth3.mm"
include "cardid2.mm"
include "mp2b.mm"

theorem cardid
  let cA: class A
  let vx: setvar x
  assume cardval.1: |- A e. _V


  assert |- ( card ` A ) ~~ A

  proof
    cA
    cvv
    wcel
    cA
    ccrd
    cdm
    wcel
    cA
    ccrd
    cfv
    cA
    cen
    wbr
    cardval.1
    cA
    cvv
    numth3
    cA
    cardid2
    mp2b
end
