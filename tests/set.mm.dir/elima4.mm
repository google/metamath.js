include "cima.mm"
include "wcel.mm"
include "cvv.mm"
include "csn.mm"
include "cxp.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "elex.mm"
include "wceq.mm"
include "xpeq2.mm"
include "xp0.mm"
include "syl6eq.mm"
include "ineq2d.mm"
include "in0.mm"
include "necon3i.mm"
include "snnzb.mm"
include "sylibr.mm"
include "cv.mm"
include "eleq1.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "neeq1d.mm"
include "wex.mm"
include "cop.mm"
include "wa.mm"
include "elin.mm"
include "ancom.mm"
include "elxp.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "exbii.mm"
include "anass.mm"
include "2exbii.mm"
include "19.41vv.mm"
include "bitr3i.mm"
include "exrot3.mm"
include "weq.mm"
include "opex.mm"
include "anbi2d.mm"
include "ceqsexv.mm"
include "an12.mm"
include "velsn.mm"
include "vex.mm"
include "opeq2.mm"
include "eleq1d.mm"
include "n0.mm"
include "elima3.mm"
include "3bitr4ri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem elima4
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. ( R " B ) <-> ( R i^i ( B X. { A } ) ) =/= (/) )

  proof
    cA
    cR
    cB
    cima
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cR
    cB
    cA
    csn
    #
    cxp
    #
    cin
    #
    c0
    wne
    #
    cA
    @0
    elex
    @6
    @3
    c0
    wne
    @2
    @3
    c0
    @5
    c0
    @3
    c0
    wceq
    #
    @5
    cR
    c0
    cin
    c0
    @7
    @4
    c0
    cR
    @7
    @4
    cB
    c0
    cxp
    c0
    @3
    c0
    cB
    xpeq2
    cB
    xp0
    syl6eq
    ineq2d
    cR
    in0
    syl6eq
    necon3i
    cA
    snnzb
    sylibr
    vx
    cv
    #
    @0
    wcel
    #
    cR
    cB
    @8
    csn
    #
    cxp
    #
    cin
    #
    c0
    wne
    #
    @1
    @6
    vx
    cA
    cvv
    @8
    cA
    @0
    eleq1
    @8
    cA
    wceq
    #
    @12
    @5
    c0
    @14
    @11
    @4
    cR
    @14
    @10
    @3
    cB
    @8
    cA
    sneq
    xpeq2d
    ineq2d
    neeq1d
    vp
    cv
    #
    @12
    wcel
    #
    vp
    wex
    #
    vy
    cv
    #
    cB
    wcel
    #
    @18
    @8
    cop
    #
    cR
    wcel
    #
    wa
    #
    vy
    wex
    #
    @13
    @9
    @17
    @15
    @18
    vz
    cv
    #
    cop
    #
    wceq
    #
    @19
    @24
    @10
    wcel
    #
    wa
    #
    wa
    #
    vz
    wex
    vy
    wex
    #
    @15
    cR
    wcel
    #
    wa
    #
    vp
    wex
    #
    @26
    @28
    @31
    wa
    #
    wa
    #
    vp
    wex
    #
    vz
    wex
    #
    vy
    wex
    #
    @23
    @16
    @32
    vp
    @16
    @31
    @15
    @11
    wcel
    #
    wa
    @39
    @31
    wa
    @32
    @15
    cR
    @11
    elin
    @31
    @39
    ancom
    @39
    @30
    @31
    vy
    vz
    @15
    cB
    @10
    elxp
    anbi1i
    3bitri
    exbii
    @33
    @35
    vz
    wex
    vy
    wex
    #
    vp
    wex
    @38
    @40
    @32
    vp
    @40
    @29
    @31
    wa
    #
    vz
    wex
    vy
    wex
    @32
    @41
    @35
    vy
    vz
    @26
    @28
    @31
    anass
    2exbii
    @29
    @31
    vy
    vz
    19.41vv
    bitr3i
    exbii
    @35
    vp
    vy
    vz
    exrot3
    bitr3i
    @37
    @22
    vy
    @37
    @28
    @25
    cR
    wcel
    #
    wa
    #
    vz
    wex
    vz
    vx
    weq
    #
    @19
    @42
    wa
    #
    wa
    #
    vz
    wex
    @22
    @36
    @43
    vz
    @34
    @43
    vp
    @25
    @18
    @24
    opex
    @26
    @31
    @42
    @28
    @15
    @25
    cR
    eleq1
    anbi2d
    ceqsexv
    exbii
    @43
    @46
    vz
    @43
    @19
    @27
    @42
    wa
    wa
    @27
    @45
    wa
    @46
    @19
    @27
    @42
    anass
    @19
    @27
    @42
    an12
    @27
    @44
    @45
    vz
    @8
    velsn
    anbi1i
    3bitri
    exbii
    @45
    @22
    vz
    @8
    vx
    vex
    #
    @44
    @42
    @21
    @19
    @44
    @25
    @20
    cR
    @24
    @8
    @18
    opeq2
    eleq1d
    anbi2d
    ceqsexv
    3bitri
    exbii
    3bitri
    vp
    @12
    n0
    vy
    @8
    cR
    cB
    @47
    elima3
    3bitr4ri
    vtoclbg
    pm5.21nii
end
