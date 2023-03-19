include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "finnum.mm"
include "cardid2.mm"
include "syl.mm"

theorem ficardid
  let cA: class A
  let vx: setvar x


  assert |- ( A e. Fin -> ( card ` A ) ~~ A )

  proof
    cA
    cfn
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
    finnum
    cA
    cardid2
    syl
end
