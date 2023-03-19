include "wcel.mm"
include "w3a.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccnv.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "brcnvg.mm"
include "3adant1.mm"
include "brtrclfv.mm"
include "3ad2ant1.mm"
include "bitrd.mm"

theorem brcnvtrclfv
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
  assert |- ( ( R e. U /\ A e. V /\ B e. W ) -> ( A `' ( t+ ` R ) B <-> A. r ( ( R C_ r /\ ( r o. r ) C_ r ) -> B r A ) ) )

  proof
    cR
    cU
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    w3a
    cA
    cB
    cR
    ctcl
    cfv
    #
    ccnv
    wbr
    #
    cB
    cA
    @3
    wbr
    #
    cR
    vr
    cv
    #
    wss
    @6
    @6
    ccom
    @6
    wss
    wa
    cB
    cA
    @6
    wbr
    wi
    vr
    wal
    #
    @1
    @2
    @4
    @5
    wb
    @0
    cA
    cB
    cV
    cW
    @3
    brcnvg
    3adant1
    @0
    @1
    @5
    @7
    wb
    @2
    cB
    cA
    cR
    cU
    vr
    brtrclfv
    3ad2ant1
    bitrd
end
