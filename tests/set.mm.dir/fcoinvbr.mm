include "wfn.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "ccnv.mm"
include "wa.mm"
include "wex.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "ccom.mm"
include "breqi.mm"
include "brcog.mm"
include "syl5bb.mm"
include "3adant1.mm"
include "fvex.mm"
include "eqvinc.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "exbii.mm"
include "bitri.mm"
include "fnbrfvb.mm"
include "3adant3.mm"
include "3adant2.mm"
include "anbi12d.mm"
include "cvv.mm"
include "vex.mm"
include "brcnvg.mm"
include "mpan.mm"
include "3ad2ant3.mm"
include "anbi2d.mm"
include "bitr4d.mm"
include "exbidv.mm"

theorem fcoinvbr
  let cA: class A
  let c.sm: class .~
  let cF: class F
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume fcoinvbr.e: |- .~ = ( `' F o. F )


  assert |- ( ( F Fn A /\ X e. A /\ Y e. A ) -> ( X .~ Y <-> ( F ` X ) = ( F ` Y ) ) )

  proof
    cF
    cA
    wfn
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    w3a
    #
    cX
    cY
    c.sm
    wbr
    #
    cX
    vz
    cv
    #
    cF
    wbr
    #
    @5
    cY
    cF
    ccnv
    #
    wbr
    #
    wa
    #
    vz
    wex
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    wceq
    #
    @1
    @2
    @4
    @10
    wb
    @0
    @4
    cX
    cY
    @7
    cF
    ccom
    #
    wbr
    @1
    @2
    wa
    @10
    cX
    cY
    c.sm
    @14
    fcoinvbr.e
    breqi
    vz
    cX
    cY
    @7
    cF
    cA
    cA
    brcog
    syl5bb
    3adant1
    @13
    @11
    @5
    wceq
    #
    @12
    @5
    wceq
    #
    wa
    #
    vz
    wex
    #
    @3
    @10
    @13
    @5
    @11
    wceq
    #
    @5
    @12
    wceq
    #
    wa
    #
    vz
    wex
    @18
    vz
    @11
    @12
    cX
    cF
    fvex
    eqvinc
    @21
    @17
    vz
    @19
    @15
    @20
    @16
    @5
    @11
    eqcom
    @5
    @12
    eqcom
    anbi12i
    exbii
    bitri
    @3
    @17
    @9
    vz
    @3
    @17
    @6
    cY
    @5
    cF
    wbr
    #
    wa
    @9
    @3
    @15
    @6
    @16
    @22
    @0
    @1
    @15
    @6
    wb
    @2
    cA
    cX
    @5
    cF
    fnbrfvb
    3adant3
    @0
    @2
    @16
    @22
    wb
    @1
    cA
    cY
    @5
    cF
    fnbrfvb
    3adant2
    anbi12d
    @3
    @8
    @22
    @6
    @2
    @0
    @8
    @22
    wb
    #
    @1
    @5
    cvv
    wcel
    @2
    @23
    vz
    vex
    @5
    cY
    cvv
    cA
    cF
    brcnvg
    mpan
    3ad2ant3
    anbi2d
    bitr4d
    exbidv
    syl5bb
    bitr4d
end
