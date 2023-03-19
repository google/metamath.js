include "com.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "con0.mm"
include "cdm.mm"
include "nnon.mm"
include "onenon.mm"
include "cardid2.mm"
include "3syl.mm"
include "wb.mm"
include "cfn.mm"
include "nnfi.mm"
include "ficardom.mm"
include "syl.mm"
include "nneneq.mm"
include "mpancom.mm"
include "mpbid.mm"

theorem cardnn
  let cA: class A
  let vx: setvar x


  assert |- ( A e. _om -> ( card ` A ) = A )

  proof
    cA
    com
    wcel
    #
    cA
    ccrd
    cfv
    #
    cA
    cen
    wbr
    #
    @1
    cA
    wceq
    #
    @0
    cA
    con0
    wcel
    cA
    ccrd
    cdm
    wcel
    @2
    cA
    nnon
    cA
    onenon
    cA
    cardid2
    3syl
    @1
    com
    wcel
    #
    @0
    @2
    @3
    wb
    @0
    cA
    cfn
    wcel
    @4
    cA
    nnfi
    cA
    ficardom
    syl
    @1
    cA
    nneneq
    mpancom
    mpbid
end
