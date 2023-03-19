include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "ccrd.mm"
include "wf.mm"
include "wfn.mm"
include "cxp.mm"
include "wss.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "cvv.mm"
include "crab.mm"
include "cint.mm"
include "df-card.mm"
include "funmpt2.mm"
include "wcel.mm"
include "rabab.mm"
include "dmmpt.mm"
include "intexrab.mm"
include "abbii.mm"
include "3eqtr4i.mm"
include "df-fn.mm"
include "mpbir2an.mm"
include "wa.mm"
include "copab.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "vex.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "sylibr.mm"
include "rabn0.mm"
include "sylib.mm"
include "breq2.mm"
include "rexbidv.mm"
include "elab.mm"
include "ssrab2.mm"
include "oninton.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "jca.mm"
include "ssopab2i.mm"
include "cmpt.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "df-xp.mm"
include "3sstr4i.mm"
include "dff2.mm"

theorem cardf2
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  assert |- card : { x | E. y e. On y ~~ x } --> On

  proof
    vy
    cv
    #
    vx
    cv
    #
    cen
    wbr
    #
    vy
    con0
    wrex
    #
    vx
    cab
    #
    con0
    ccrd
    wf
    ccrd
    @4
    wfn
    #
    ccrd
    @4
    con0
    cxp
    #
    wss
    @5
    ccrd
    wfun
    ccrd
    cdm
    #
    @4
    wceq
    vx
    cvv
    @2
    vy
    con0
    crab
    cint
    #
    ccrd
    vx
    vy
    df-card
    #
    funmpt2
    @8
    cvv
    wcel
    #
    vx
    cvv
    crab
    @10
    vx
    cab
    @7
    @4
    @10
    vx
    rabab
    vx
    cvv
    @8
    ccrd
    @9
    dmmpt
    @3
    @10
    vx
    @2
    vy
    con0
    intexrab
    abbii
    3eqtr4i
    ccrd
    @4
    df-fn
    mpbir2an
    vz
    cv
    #
    cvv
    wcel
    #
    vw
    cv
    #
    @0
    @11
    cen
    wbr
    #
    vy
    con0
    crab
    #
    cint
    #
    wceq
    #
    wa
    #
    vz
    vw
    copab
    #
    @11
    @4
    wcel
    #
    @13
    con0
    wcel
    #
    wa
    #
    vz
    vw
    copab
    ccrd
    @6
    @18
    @22
    vz
    vw
    @18
    @20
    @21
    @18
    @14
    vy
    con0
    wrex
    #
    @20
    @18
    @15
    c0
    wne
    #
    @23
    @18
    @16
    cvv
    wcel
    @24
    @18
    @16
    @13
    cvv
    @12
    @17
    simpr
    #
    vw
    vex
    syl6eqelr
    @15
    intex
    sylibr
    #
    @14
    vy
    con0
    rabn0
    sylib
    @3
    @23
    vx
    @11
    vz
    vex
    @1
    @11
    wceq
    @2
    @14
    vy
    con0
    @1
    @11
    @0
    cen
    breq2
    rexbidv
    elab
    sylibr
    @18
    @13
    @16
    con0
    @25
    @18
    @15
    con0
    wss
    @24
    @16
    con0
    wcel
    @14
    vy
    con0
    ssrab2
    @26
    @15
    oninton
    sylancr
    eqeltrd
    jca
    ssopab2i
    ccrd
    vz
    cvv
    @16
    cmpt
    @19
    vz
    vy
    df-card
    vz
    vw
    cvv
    @16
    df-mpt
    eqtri
    vz
    vw
    @4
    con0
    df-xp
    3sstr4i
    @4
    con0
    ccrd
    dff2
    mpbir2an
end
