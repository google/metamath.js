include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "cdm.mm"
include "cpw.mm"
include "wral.mm"
include "crn.mm"
include "wss.mm"
include "wbr.mm"
include "wex.mm"
include "w3a.mm"
include "csuc.mm"
include "com.mm"
include "cab.mm"
include "wceq.mm"
include "neeq1.mm"
include "abn0.mm"
include "syl6bb.mm"
include "eleq2.mm"
include "breq2.mm"
include "cbvabv.mm"
include "eleq2i.mm"
include "syl6bbr.mm"
include "fvex.mm"
include "elab.mm"
include "fveq2.mm"
include "breq2d.mm"
include "bitrd.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "vex.mm"
include "brelrn.mm"
include "abssi.mm"
include "sstr.mm"
include "mpan.mm"
include "dmex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "syl11.mm"
include "3imp.mm"
include "cvv.mm"
include "nfcv.mm"
include "breq1.mm"
include "abbidv.mm"
include "fveq2d.mm"
include "frsucmpt.mm"
include "mpan2.mm"
include "syl5ibrcom.mm"

theorem axdclem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let cF: class F
  let cK: class K
  let vs: setvar s
  let vw: setvar w
  assume axdclem.1: |- F = ( rec ( ( y e. _V |-> ( g ` { z | y x z } ) ) , s ) |` _om )

  disjoint F y
  disjoint F z
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint g y
  disjoint s y
  disjoint x y
  disjoint x z
  disjoint F w
  disjoint w y
  disjoint w z
  disjoint K w
  disjoint g w
  disjoint s w
  disjoint w x
  assert |- ( ( A. y e. ~P dom x ( y =/= (/) -> ( g ` y ) e. y ) /\ ran x C_ dom x /\ E. z ( F ` K ) x z ) -> ( K e. _om -> ( F ` K ) x ( F ` suc K ) ) )

  proof
    vy
    cv
    #
    c0
    wne
    #
    @0
    vg
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vy
    vx
    cv
    #
    cdm
    #
    cpw
    #
    wral
    #
    @6
    crn
    #
    @7
    wss
    #
    cK
    cF
    cfv
    #
    vz
    cv
    #
    @6
    wbr
    #
    vz
    wex
    #
    w3a
    @12
    cK
    csuc
    cF
    cfv
    #
    @6
    wbr
    cK
    com
    wcel
    #
    @12
    @14
    vz
    cab
    #
    @2
    cfv
    #
    @6
    wbr
    #
    @9
    @11
    @15
    @20
    @18
    @8
    wcel
    #
    @9
    @15
    @20
    wi
    #
    @11
    @5
    @22
    vy
    @18
    @8
    @0
    @18
    wceq
    #
    @1
    @15
    @4
    @20
    @23
    @1
    @18
    c0
    wne
    @15
    @0
    @18
    c0
    neeq1
    @14
    vz
    abn0
    syl6bb
    @23
    @4
    @12
    @3
    @6
    wbr
    #
    @20
    @23
    @4
    @3
    @12
    vw
    cv
    #
    @6
    wbr
    #
    vw
    cab
    #
    wcel
    #
    @24
    @23
    @4
    @3
    @18
    wcel
    @28
    @0
    @18
    @3
    eleq2
    @27
    @18
    @3
    @26
    @14
    vw
    vz
    @25
    @13
    @12
    @6
    breq2
    cbvabv
    eleq2i
    syl6bbr
    @26
    @24
    vw
    @3
    @0
    @2
    fvex
    @25
    @3
    @12
    @6
    breq2
    elab
    syl6bb
    @23
    @3
    @19
    @12
    @6
    @0
    @18
    @2
    fveq2
    breq2d
    bitrd
    imbi12d
    rspcv
    @11
    @18
    @7
    wss
    #
    @21
    @18
    @10
    wss
    @11
    @29
    @14
    vz
    @10
    @12
    @13
    @6
    cK
    cF
    fvex
    vz
    vex
    brelrn
    abssi
    @18
    @10
    @7
    sstr
    mpan
    @18
    @7
    @6
    vx
    vex
    dmex
    elpw2
    sylibr
    syl11
    3imp
    @17
    @16
    @19
    @12
    @6
    @17
    @19
    cvv
    wcel
    @16
    @19
    wceq
    @18
    @2
    fvex
    vy
    vs
    cv
    #
    cK
    @0
    @13
    @6
    wbr
    #
    vz
    cab
    #
    @2
    cfv
    @19
    cF
    cvv
    vy
    @30
    nfcv
    vy
    cK
    nfcv
    vy
    @19
    nfcv
    axdclem.1
    @0
    @12
    wceq
    #
    @32
    @18
    @2
    @33
    @31
    @14
    vz
    @0
    @12
    @13
    @6
    breq1
    abbidv
    fveq2d
    frsucmpt
    mpan2
    breq2d
    syl5ibrcom
end
