include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "cres.mm"
include "idinxpres.mm"
include "sseq1i.mm"
include "issref.mm"
include "brinxp2ALTV.mm"
include "pm4.24.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "3bitri.mm"
include "ralanid.mm"
include "bitri.mm"

theorem idinxpssinxp2
  let vx: setvar x
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint R x
  assert |- ( ( _I i^i ( A X. A ) ) C_ ( R i^i ( A X. A ) ) <-> A. x e. A x R x )

  proof
    cid
    cA
    cA
    cxp
    #
    cin
    #
    cR
    @0
    cin
    #
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    @4
    @4
    cR
    wbr
    #
    wa
    #
    vx
    cA
    wral
    #
    @6
    vx
    cA
    wral
    @3
    cid
    cA
    cres
    #
    @2
    wss
    @4
    @4
    @2
    wbr
    #
    vx
    cA
    wral
    @8
    @1
    @9
    @2
    cA
    idinxpres
    sseq1i
    vx
    cA
    @2
    issref
    @10
    @7
    vx
    cA
    @10
    @5
    @5
    wa
    #
    @6
    wa
    @7
    cA
    cA
    @4
    @4
    cR
    brinxp2ALTV
    @5
    @11
    @6
    @5
    pm4.24
    anbi1i
    bitr4i
    ralbii
    3bitri
    @6
    vx
    cA
    ralanid
    bitri
end
