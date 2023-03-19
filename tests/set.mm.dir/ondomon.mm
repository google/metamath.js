include "wcel.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "word.mm"
include "wtr.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "onelon.mm"
include "cvv.mm"
include "vex.mm"
include "onelss.mm"
include "imp.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "jca.mm"
include "domtr.mm"
include "anim2i.mm"
include "anassrs.mm"
include "sylan.mm"
include "exp31.mm"
include "com12.mm"
include "impd.mm"
include "breq1.mm"
include "elrab.mm"
include "3imtr4g.mm"
include "gen2.mm"
include "dftr2.mm"
include "mpbir.mm"
include "ssrab2.mm"
include "ordon.mm"
include "trssord.mm"
include "mp3an.mm"
include "wb.mm"
include "cpw.mm"
include "csdm.mm"
include "wral.mm"
include "elex.mm"
include "canth2g.mm"
include "domsdomtr.mm"
include "sylan2.mm"
include "expcom.mm"
include "ralrimivw.mm"
include "syl.mm"
include "ss2rab.mm"
include "sylibr.mm"
include "ccrd.mm"
include "cfv.mm"
include "cdm.mm"
include "wceq.mm"
include "pwexg.mm"
include "numth3.mm"
include "cardval2.mm"
include "3syl.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "ssexg.mm"
include "syl2anc.mm"
include "elong.mm"
include "mpbiri.mm"

theorem ondomon
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. V -> { x e. On | x ~<_ A } e. On )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    cA
    cdom
    wbr
    #
    vx
    con0
    crab
    #
    con0
    wcel
    #
    @3
    word
    #
    @3
    wtr
    #
    @3
    con0
    wss
    con0
    word
    @5
    @6
    vy
    cv
    #
    vz
    cv
    #
    wcel
    #
    @8
    @3
    wcel
    #
    wa
    @7
    @3
    wcel
    #
    wi
    #
    vz
    wal
    vy
    wal
    @12
    vy
    vz
    @9
    @10
    @11
    @9
    @8
    con0
    wcel
    #
    @8
    cA
    cdom
    wbr
    #
    wa
    @7
    con0
    wcel
    #
    @7
    cA
    cdom
    wbr
    #
    wa
    #
    @10
    @11
    @9
    @13
    @14
    @17
    @13
    @9
    @14
    @17
    wi
    @13
    @9
    @14
    @17
    @13
    @9
    wa
    #
    @15
    @7
    @8
    cdom
    wbr
    #
    wa
    @14
    @17
    @18
    @15
    @19
    @8
    @7
    onelon
    @8
    cvv
    wcel
    @18
    @7
    @8
    wss
    #
    @19
    vz
    vex
    @13
    @9
    @20
    @8
    @7
    onelss
    imp
    @7
    @8
    cvv
    ssdomg
    mpsyl
    jca
    @15
    @19
    @14
    @17
    @19
    @14
    wa
    @16
    @15
    @7
    @8
    cA
    domtr
    anim2i
    anassrs
    sylan
    exp31
    com12
    impd
    @2
    @14
    vx
    @8
    con0
    @1
    @8
    cA
    cdom
    breq1
    elrab
    @2
    @16
    vx
    @7
    con0
    @1
    @7
    cA
    cdom
    breq1
    elrab
    3imtr4g
    imp
    gen2
    vy
    vz
    @3
    dftr2
    mpbir
    @2
    vx
    con0
    ssrab2
    ordon
    @3
    con0
    trssord
    mp3an
    @0
    @3
    cvv
    wcel
    #
    @4
    @5
    wb
    @0
    @3
    @1
    cA
    cpw
    #
    csdm
    wbr
    #
    vx
    con0
    crab
    #
    wss
    #
    @24
    cvv
    wcel
    @21
    @0
    @2
    @23
    wi
    #
    vx
    con0
    wral
    #
    @25
    @0
    cA
    cvv
    wcel
    #
    @27
    cA
    cV
    elex
    @28
    @26
    vx
    con0
    @2
    @28
    @23
    @28
    @2
    cA
    @22
    csdm
    wbr
    @23
    cA
    cvv
    canth2g
    @1
    cA
    @22
    domsdomtr
    sylan2
    expcom
    ralrimivw
    syl
    @2
    @23
    vx
    con0
    ss2rab
    sylibr
    @0
    @24
    @22
    ccrd
    cfv
    #
    cvv
    @0
    @22
    cvv
    wcel
    @22
    ccrd
    cdm
    wcel
    @29
    @24
    wceq
    cA
    cV
    pwexg
    @22
    cvv
    numth3
    vx
    @22
    cardval2
    3syl
    @22
    ccrd
    fvex
    syl6eqelr
    @3
    @24
    cvv
    ssexg
    syl2anc
    @3
    cvv
    elong
    syl
    mpbiri
end
