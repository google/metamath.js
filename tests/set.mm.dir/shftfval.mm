include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "copab.mm"
include "cvv.mm"
include "cshi.mm"
include "wceq.mm"
include "caddc.mm"
include "cdm.mm"
include "wrex.mm"
include "cab.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "ovex.mm"
include "vex.mm"
include "breldm.mm"
include "npcan.mm"
include "eqcomd.mm"
include "ancoms.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anr.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "brelrn.mm"
include "adantl.mm"
include "jca.mm"
include "expl.mm"
include "ssopab2dv.mm"
include "df-xp.mm"
include "syl6sseqr.mm"
include "dmex.mm"
include "abrexex.mm"
include "rnex.mm"
include "xpex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "breq.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "oveq2.mm"
include "breq1d.mm"
include "df-shft.mm"
include "ovmpt2g.mm"
include "mp3an1.mm"
include "mpdan.mm"

theorem shftfval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  assume shftfval.1: |- F e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F w
  disjoint F z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( A e. CC -> ( F shift A ) = { <. x , y >. | ( x e. CC /\ ( x - A ) F y ) } )

  proof
    cA
    cc
    wcel
    #
    vx
    cv
    #
    cc
    wcel
    #
    @1
    cA
    cmin
    co
    #
    vy
    cv
    #
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    cvv
    wcel
    #
    cF
    cA
    cshi
    co
    @7
    wceq
    #
    @0
    @7
    vz
    cv
    #
    vw
    cv
    #
    cA
    caddc
    co
    #
    wceq
    #
    vw
    cF
    cdm
    #
    wrex
    #
    vz
    cab
    #
    cF
    crn
    #
    cxp
    #
    wss
    @18
    cvv
    wcel
    @8
    @0
    @7
    @1
    @16
    wcel
    #
    @4
    @17
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @18
    @0
    @6
    @21
    vx
    vy
    @0
    @2
    @5
    @21
    @0
    @2
    wa
    #
    @5
    wa
    #
    @19
    @20
    @23
    @1
    @12
    wceq
    #
    vw
    @14
    wrex
    #
    @19
    @5
    @3
    @14
    wcel
    @1
    @3
    cA
    caddc
    co
    #
    wceq
    #
    @25
    @22
    @3
    @4
    cF
    @1
    cA
    cmin
    ovex
    #
    vy
    vex
    #
    breldm
    @2
    @0
    @27
    @2
    @0
    wa
    @26
    @1
    @1
    cA
    npcan
    eqcomd
    ancoms
    @24
    @27
    vw
    @3
    @14
    @11
    @3
    wceq
    @12
    @26
    @1
    @11
    @3
    cA
    caddc
    oveq1
    eqeq2d
    rspcev
    syl2anr
    @15
    @25
    vz
    @1
    vx
    vex
    @10
    @1
    wceq
    @13
    @24
    vw
    @14
    @10
    @1
    @12
    eqeq1
    rexbidv
    elab
    sylibr
    @5
    @20
    @22
    @3
    @4
    cF
    @28
    @29
    brelrn
    adantl
    jca
    expl
    ssopab2dv
    vx
    vy
    @16
    @17
    df-xp
    syl6sseqr
    @16
    @17
    vw
    vz
    @14
    @12
    cF
    shftfval.1
    dmex
    abrexex
    cF
    shftfval.1
    rnex
    xpex
    @7
    @18
    cvv
    ssexg
    sylancl
    cF
    cvv
    wcel
    @0
    @8
    @9
    shftfval.1
    vz
    vw
    cF
    cA
    cvv
    cc
    @2
    @1
    @11
    cmin
    co
    #
    @4
    @10
    wbr
    #
    wa
    #
    vx
    vy
    copab
    @7
    cshi
    @2
    @30
    @4
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    cvv
    @10
    cF
    wceq
    #
    @32
    @34
    vx
    vy
    @35
    @31
    @33
    @2
    @30
    @4
    @10
    cF
    breq
    anbi2d
    opabbidv
    @11
    cA
    wceq
    #
    @34
    @6
    vx
    vy
    @36
    @33
    @5
    @2
    @36
    @30
    @3
    @4
    cF
    @11
    cA
    @1
    cmin
    oveq2
    breq1d
    anbi2d
    opabbidv
    vw
    vx
    vy
    vz
    df-shft
    ovmpt2g
    mp3an1
    mpdan
end
