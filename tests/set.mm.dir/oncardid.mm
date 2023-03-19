include "con0.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "onenon.mm"
include "cardid2.mm"
include "syl.mm"

theorem oncardid
  let cA: class A
  let vx: setvar x


  assert |- ( A e. On -> ( card ` A ) ~~ A )

  proof
    cA
    con0
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
    cA
    onenon
    cA
    cardid2
    syl
end
