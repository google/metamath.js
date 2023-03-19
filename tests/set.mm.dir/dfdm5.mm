include "cdm.mm"
include "c1st.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "cima.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "excom.mm"
include "weq.mm"
include "opex.mm"
include "breq1.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "vex.mm"
include "br1steq.mm"
include "equcom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "syl6bb.mm"
include "ceqsexv.mm"
include "exbii.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "3bitr3ri.mm"
include "ancom.mm"
include "anass.mm"
include "brres.mm"
include "elvv.mm"
include "19.41vv.mm"
include "3bitr4i.mm"
include "eldm2.mm"
include "elima2.mm"
include "eqriv.mm"

theorem dfdm5
  let cA: class A
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- dom A = ( ( 1st |` ( _V X. _V ) ) " A )

  proof
    vx
    cA
    cdm
    #
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    cA
    cima
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cA
    wcel
    #
    vy
    wex
    #
    vp
    cv
    #
    cA
    wcel
    #
    @9
    @4
    @2
    wbr
    #
    wa
    #
    vp
    wex
    #
    @4
    @0
    wcel
    @4
    @3
    wcel
    @9
    vz
    cv
    #
    @5
    cop
    #
    wceq
    #
    @9
    @4
    c1st
    wbr
    #
    @10
    wa
    #
    wa
    #
    vz
    wex
    #
    vp
    wex
    #
    vy
    wex
    @20
    vy
    wex
    #
    vp
    wex
    @8
    @13
    @20
    vy
    vp
    excom
    @7
    @21
    vy
    @19
    vp
    wex
    #
    vz
    wex
    vz
    vx
    weq
    #
    @15
    cA
    wcel
    #
    wa
    #
    vz
    wex
    @21
    @7
    @23
    @26
    vz
    @18
    @26
    vp
    @15
    @14
    @5
    opex
    @16
    @18
    @15
    @4
    c1st
    wbr
    #
    @25
    wa
    @26
    @16
    @17
    @27
    @10
    @25
    @9
    @15
    @4
    c1st
    breq1
    @9
    @15
    cA
    eleq1
    anbi12d
    @27
    @24
    @25
    @27
    vx
    vz
    weq
    @24
    @14
    @5
    @4
    vz
    vex
    vy
    vex
    br1steq
    vx
    vz
    equcom
    bitri
    anbi1i
    syl6bb
    ceqsexv
    exbii
    @19
    vz
    vp
    excom
    @25
    @7
    vz
    @4
    vx
    vex
    #
    @24
    @15
    @6
    cA
    @14
    @4
    @5
    opeq1
    eleq1d
    ceqsexv
    3bitr3ri
    exbii
    @12
    @22
    vp
    @12
    @11
    @10
    wa
    #
    @22
    @10
    @11
    ancom
    @16
    vz
    wex
    vy
    wex
    #
    @17
    wa
    #
    @10
    wa
    @30
    @18
    wa
    @29
    @22
    @30
    @17
    @10
    anass
    @11
    @31
    @10
    @11
    @17
    @9
    @1
    wcel
    #
    wa
    #
    @31
    @9
    @4
    c1st
    @1
    @28
    brres
    @33
    @32
    @17
    wa
    @31
    @17
    @32
    ancom
    @32
    @30
    @17
    @32
    @16
    vy
    wex
    vz
    wex
    @30
    vz
    vy
    @9
    elvv
    @16
    vz
    vy
    excom
    bitri
    anbi1i
    bitri
    bitri
    anbi1i
    @16
    @18
    vy
    vz
    19.41vv
    3bitr4i
    bitri
    exbii
    3bitr4i
    vy
    @4
    cA
    @28
    eldm2
    vp
    @4
    @2
    cA
    @28
    elima2
    3bitr4i
    eqriv
end
