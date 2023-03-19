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
include "brtrclfv.mm"
include "syl.mm"

theorem brtrclfvcnv
  let cA: class A
  let cB: class B
  let cR: class R
  let cV: class V
  let vr: setvar r

  disjoint A r
  disjoint B r
  disjoint R r
  assert |- ( R e. V -> ( A ( t+ ` `' R ) B <-> A. r ( ( `' R C_ r /\ ( r o. r ) C_ r ) -> A r B ) ) )

  proof
    cR
    cV
    wcel
    cR
    ccnv
    #
    cvv
    wcel
    cA
    cB
    @0
    ctcl
    cfv
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
    cA
    cB
    @1
    wbr
    wi
    vr
    wal
    wb
    cR
    cV
    cnvexg
    cA
    cB
    @0
    cvv
    vr
    brtrclfv
    syl
end
