include "wcel.mm"
include "ccnv.mm"
include "cvv.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "cnvexg.mm"
include "brcnvtrclfv.mm"
include "syl3an1.mm"

theorem brcnvtrclfvcnv
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let vr: setvar r

  disjoint A r
  disjoint B r
  disjoint R r
  assert |- ( ( R e. U /\ A e. V /\ B e. W ) -> ( A `' ( t+ ` `' R ) B <-> A. r ( ( `' R C_ r /\ ( r o. r ) C_ r ) -> B r A ) ) )

  proof
    cR
    cU
    wcel
    cR
    ccnv
    #
    cvv
    wcel
    cA
    cV
    wcel
    cB
    cW
    wcel
    cA
    cB
    @0
    ctcl
    cfv
    ccnv
    wbr
    @0
    vr
    cv
    #
    wss
    @1
    @1
    ccom
    @1
    wss
    wa
    cB
    cA
    @1
    wbr
    wi
    vr
    wal
    wb
    cR
    cU
    cnvexg
    cA
    cB
    @0
    cvv
    cV
    cW
    vr
    brcnvtrclfv
    syl3an1
end
