include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "cint.mm"
include "cop.mm"
include "snex.mm"
include "xpex.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "elxp.mm"
include "inteq.mm"
include "inteqd.mm"
include "vex.mm"
include "op1stb.mm"
include "syl6eq.mm"
include "syl6eqel.mm"
include "adantr.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "opex.mm"
include "a1i.mm"
include "wb.mm"
include "eqvisset.mm"
include "ancom.mm"
include "anass.mm"
include "velsn.mm"
include "anbi1i.mm"
include "3bitr3i.mm"
include "exbii.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "ceqsexv.mm"
include "syl6req.mm"
include "pm4.71ri.mm"
include "bitri.mm"
include "3bitri.mm"
include "opeq1.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "ceqsexgv.mm"
include "syl5bb.mm"
include "syl.mm"
include "pm5.32ri.mm"
include "pm4.71i.mm"
include "bitr2i.mm"
include "en2i.mm"

theorem xpsnen
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xpsnen.1: |- A e. _V
  assume xpsnen.2: |- B e. _V


  assert |- ( A X. { B } ) ~~ A

  proof
    vy
    vx
    cA
    cB
    csn
    #
    cxp
    #
    cA
    vy
    cv
    #
    cint
    #
    cint
    #
    vx
    cv
    #
    cB
    cop
    #
    cA
    @0
    xpsnen.1
    cB
    snex
    xpex
    xpsnen.1
    @2
    @1
    wcel
    #
    @2
    @5
    vz
    cv
    #
    cop
    #
    wceq
    #
    @5
    cA
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    #
    wa
    #
    vz
    wex
    #
    vx
    wex
    #
    @4
    cvv
    wcel
    #
    vx
    vz
    @2
    cA
    @0
    elxp
    #
    @14
    @17
    vx
    vz
    @10
    @17
    @13
    @10
    @4
    @5
    cvv
    @10
    @4
    @9
    cint
    #
    cint
    @5
    @10
    @3
    @19
    @2
    @9
    inteq
    inteqd
    @5
    @8
    vx
    vex
    #
    vz
    vex
    op1stb
    syl6eq
    @20
    syl6eqel
    adantr
    exlimivv
    sylbi
    @6
    cvv
    wcel
    @11
    @5
    cB
    opex
    a1i
    @7
    @5
    @4
    wceq
    #
    wa
    @2
    @4
    cB
    cop
    #
    wceq
    #
    @4
    cA
    wcel
    #
    wa
    #
    @21
    wa
    #
    @2
    @6
    wceq
    #
    @11
    wa
    #
    @11
    @27
    wa
    @21
    @7
    @25
    @21
    @17
    @7
    @25
    wb
    vx
    @4
    eqvisset
    @7
    @21
    @28
    wa
    #
    vx
    wex
    #
    @17
    @25
    @7
    @16
    @30
    @18
    @15
    @29
    vx
    @15
    @8
    cB
    wceq
    #
    @10
    @11
    wa
    #
    wa
    #
    vz
    wex
    @28
    @29
    @14
    @33
    vz
    @32
    @12
    wa
    @12
    @32
    wa
    @14
    @33
    @32
    @12
    ancom
    @10
    @11
    @12
    anass
    @12
    @31
    @32
    vz
    cB
    velsn
    anbi1i
    3bitr3i
    exbii
    @32
    @28
    vz
    cB
    xpsnen.2
    @31
    @10
    @27
    @11
    @31
    @9
    @6
    @2
    @8
    cB
    @5
    opeq2
    eqeq2d
    anbi1d
    ceqsexv
    @28
    @21
    @27
    wa
    #
    @11
    wa
    @29
    @27
    @34
    @11
    @27
    @21
    @27
    @4
    @6
    cint
    #
    cint
    @5
    @27
    @3
    @35
    @2
    @6
    inteq
    inteqd
    @5
    cB
    @20
    xpsnen.2
    op1stb
    syl6req
    #
    pm4.71ri
    anbi1i
    @21
    @27
    @11
    anass
    bitri
    3bitri
    exbii
    bitri
    @28
    @25
    vx
    @4
    cvv
    @21
    @27
    @23
    @11
    @24
    @21
    @6
    @22
    @2
    @5
    @4
    cB
    opeq1
    eqeq2d
    @5
    @4
    cA
    eleq1
    anbi12d
    #
    ceqsexgv
    syl5bb
    syl
    pm5.32ri
    @28
    @28
    @21
    wa
    @26
    @28
    @21
    @27
    @21
    @11
    @36
    adantr
    pm4.71i
    @21
    @28
    @25
    @37
    pm5.32ri
    bitr2i
    @27
    @11
    ancom
    3bitri
    en2i
end
