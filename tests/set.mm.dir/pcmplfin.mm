include "cpcmp.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cref.mm"
include "wbr.mm"
include "cpw.mm"
include "clocfin.mm"
include "cfv.mm"
include "cin.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "simp2.mm"
include "cvv.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "3adant3.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "ctop.mm"
include "ccref.mm"
include "ispcmp.mm"
include "iscref.mm"
include "bitri.mm"
include "simprbi.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "breq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "elin.mm"
include "anbi1i.mm"
include "anass.mm"
include "rexbii2.mm"
include "sylib.mm"

theorem pcmplfin
  let vv: setvar v
  let cU: class U
  let cJ: class J
  let cX: class X
  let vu: setvar u
  assume pcmplfin.x: |- X = U. J

  disjoint J v
  disjoint U v
  disjoint J u
  disjoint u v
  disjoint U u
  disjoint X u
  assert |- ( ( J e. Paracomp /\ U C_ J /\ X = U. U ) -> E. v e. ~P J ( v e. ( LocFin ` J ) /\ v Ref U ) )

  proof
    cJ
    cpcmp
    wcel
    #
    cU
    cJ
    wss
    #
    cX
    cU
    cuni
    #
    wceq
    #
    w3a
    #
    vv
    cv
    #
    cU
    cref
    wbr
    #
    vv
    cJ
    cpw
    #
    cJ
    clocfin
    cfv
    #
    cin
    #
    wrex
    #
    @5
    @8
    wcel
    #
    @6
    wa
    #
    vv
    @7
    wrex
    @4
    cU
    @7
    wcel
    #
    cX
    vu
    cv
    #
    cuni
    #
    wceq
    #
    @5
    @14
    cref
    wbr
    #
    vv
    @9
    wrex
    #
    wi
    #
    vu
    @7
    wral
    #
    @3
    @10
    @4
    @13
    @1
    @0
    @1
    @3
    simp2
    @4
    cU
    cvv
    wcel
    #
    @13
    @1
    wb
    @0
    @1
    @21
    @3
    @1
    @0
    @21
    cU
    cJ
    cpcmp
    ssexg
    ancoms
    3adant3
    cU
    cJ
    cvv
    elpwg
    syl
    mpbird
    @0
    @1
    @20
    @3
    @0
    cJ
    ctop
    wcel
    #
    @20
    @0
    cJ
    @8
    ccref
    wcel
    @22
    @20
    wa
    cJ
    ispcmp
    vu
    vv
    @8
    cJ
    cX
    pcmplfin.x
    iscref
    bitri
    simprbi
    3ad2ant1
    @0
    @1
    @3
    simp3
    @19
    @3
    @10
    wi
    vu
    cU
    @7
    @14
    cU
    wceq
    #
    @16
    @3
    @18
    @10
    @23
    @15
    @2
    cX
    @14
    cU
    unieq
    eqeq2d
    @23
    @17
    @6
    vv
    @9
    @14
    cU
    @5
    cref
    breq2
    rexbidv
    imbi12d
    rspcv
    syl3c
    @6
    @12
    vv
    @9
    @7
    @5
    @9
    wcel
    #
    @6
    wa
    @5
    @7
    wcel
    #
    @11
    wa
    #
    @6
    wa
    @25
    @12
    wa
    @24
    @26
    @6
    @5
    @7
    @8
    elin
    anbi1i
    @25
    @11
    @6
    anass
    bitri
    rexbii2
    sylib
end
