include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "crn.mm"
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
include "dmeqd.mm"
include "op1sta.mm"
include "3bitri.mm"
include "dmex.mm"
include "opeq1.mm"
include "anbi1d.mm"

theorem elxp4
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. ( B X. C ) <-> ( A = <. U. dom { A } , U. ran { A } >. /\ ( U. dom { A } e. B /\ U. ran { A } e. C ) ) )

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
    csn
    #
    cdm
    #
    cuni
    #
    wceq
    #
    cA
    @0
    @9
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
    cA
    @11
    @14
    cop
    #
    wceq
    #
    @11
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
    @12
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
    @28
    vy
    @7
    @27
    @3
    wa
    #
    @6
    wa
    @28
    @3
    @29
    @6
    @3
    @27
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
    @31
    @3
    @9
    @30
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
    @27
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
    @9
    cA
    snex
    #
    rnex
    uniex
    #
    @27
    @3
    @16
    @6
    @18
    @27
    @2
    @15
    cA
    @1
    @14
    @0
    opeq2
    eqeq2d
    @27
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
    @26
    @18
    @16
    @12
    @16
    @11
    @15
    csn
    #
    cdm
    #
    cuni
    @0
    @16
    @10
    @36
    @16
    @9
    @35
    cA
    @15
    sneq
    dmeqd
    unieqd
    @0
    @14
    @32
    @34
    op1sta
    syl6req
    pm4.71ri
    anbi1i
    @12
    @16
    @18
    anass
    3bitri
    exbii
    @19
    @25
    vx
    @11
    @10
    @9
    @33
    dmex
    uniex
    @12
    @16
    @22
    @18
    @24
    @12
    @15
    @21
    cA
    @0
    @11
    @14
    opeq1
    eqeq2d
    @12
    @4
    @23
    @17
    @0
    @11
    cB
    eleq1
    anbi1d
    anbi12d
    ceqsexv
    3bitri
end
