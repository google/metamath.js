include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cint.mm"
include "csn.mm"
include "crn.mm"
include "cuni.mm"
include "elxp.mm"
include "sneq.mm"
include "rneqd.mm"
include "unieqd.mm"
include "vex.mm"
include "op2nda.mm"
include "syl6req.mm"
include "pm4.71ri.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "exbii.mm"
include "snex.mm"
include "rnex.mm"
include "uniex.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "anbi12d.mm"
include "ceqsexv.mm"
include "inteq.mm"
include "inteqd.mm"
include "op1stb.mm"
include "3bitri.mm"
include "cvv.mm"
include "eqvisset.mm"
include "adantr.mm"
include "exlimiv.mm"
include "elex.mm"
include "ad2antrl.mm"
include "opeq1.mm"
include "anbi1d.mm"
include "ceqsexgv.mm"
include "pm5.21nii.mm"

theorem elxp5
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ( B X. C ) <-> ( A = <. |^| |^| A , U. ran { A } >. /\ ( |^| |^| A e. B /\ U. ran { A } e. C ) ) )

  proof
    cA
    cB
    cC
    cxp
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @0
    cB
    wcel
    #
    @1
    cC
    wcel
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    @0
    cA
    cint
    #
    cint
    #
    wceq
    #
    cA
    @0
    cA
    csn
    #
    crn
    #
    cuni
    #
    cop
    #
    wceq
    #
    @4
    @14
    cC
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    vx
    wex
    #
    cA
    @10
    @14
    cop
    #
    wceq
    #
    @10
    cB
    wcel
    #
    @17
    wa
    #
    wa
    #
    vx
    vy
    cA
    cB
    cC
    elxp
    @8
    @20
    vx
    @8
    @19
    @11
    @16
    wa
    #
    @18
    wa
    @20
    @8
    @1
    @14
    wceq
    #
    @7
    wa
    #
    vy
    wex
    @19
    @7
    @29
    vy
    @7
    @28
    @3
    wa
    #
    @6
    wa
    @29
    @3
    @30
    @6
    @3
    @28
    @3
    @14
    @2
    csn
    #
    crn
    #
    cuni
    @1
    @3
    @13
    @32
    @3
    @12
    @31
    cA
    @2
    sneq
    rneqd
    unieqd
    @0
    @1
    vx
    vex
    #
    vy
    vex
    op2nda
    syl6req
    pm4.71ri
    anbi1i
    @28
    @3
    @6
    anass
    bitri
    exbii
    @7
    @19
    vy
    @14
    @13
    @12
    cA
    snex
    rnex
    uniex
    #
    @28
    @3
    @16
    @6
    @18
    @28
    @2
    @15
    cA
    @1
    @14
    @0
    opeq2
    eqeq2d
    @28
    @5
    @17
    @4
    @1
    @14
    cC
    eleq1
    anbi2d
    anbi12d
    ceqsexv
    bitri
    @16
    @27
    @18
    @16
    @11
    @16
    @10
    @15
    cint
    #
    cint
    @0
    @16
    @9
    @35
    cA
    @15
    inteq
    inteqd
    @0
    @14
    @33
    @34
    op1stb
    syl6req
    pm4.71ri
    anbi1i
    @11
    @16
    @18
    anass
    3bitri
    exbii
    @21
    @10
    cvv
    wcel
    #
    @26
    @20
    @36
    vx
    @11
    @36
    @19
    vx
    @10
    eqvisset
    adantr
    exlimiv
    @24
    @36
    @23
    @17
    @10
    cB
    elex
    ad2antrl
    @19
    @26
    vx
    @10
    cvv
    @11
    @16
    @23
    @18
    @25
    @11
    @15
    @22
    cA
    @0
    @10
    @14
    opeq1
    eqeq2d
    @11
    @4
    @24
    @17
    @0
    @10
    cB
    eleq1
    anbi1d
    anbi12d
    ceqsexgv
    pm5.21nii
    3bitri
end
