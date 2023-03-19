include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "con0.mm"
include "crab.mm"
include "word.mm"
include "wtr.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "cdom.mm"
include "onelon.mm"
include "vex.mm"
include "onelss.mm"
include "imp.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "jca.mm"
include "domsdomtr.mm"
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
include "hartogs.mm"
include "sdomdom.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "ssexg.mm"
include "mpan.mm"
include "elong.mm"
include "3syl.mm"
include "mpbiri.mm"
include "c0.mm"
include "wceq.mm"
include "0elon.mm"
include "eleq1.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "df-ne.mm"
include "rabn0.mm"
include "bitr3i.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "nsyl4.mm"
include "pm2.61i.mm"

theorem card2on
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- { x e. On | x ~< A } e. On

  proof
    cA
    cvv
    wcel
    #
    vx
    cv
    #
    cA
    csdm
    wbr
    #
    vx
    con0
    crab
    #
    con0
    wcel
    #
    @0
    @4
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
    csdm
    wbr
    #
    wa
    @7
    con0
    wcel
    #
    @7
    cA
    csdm
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
    domsdomtr
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
    csdm
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
    csdm
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
    @1
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
    cvv
    wcel
    #
    @4
    @5
    wb
    vx
    cA
    cvv
    hartogs
    @3
    @22
    wss
    @23
    @24
    @2
    @21
    vx
    con0
    @2
    @21
    wi
    @1
    con0
    wcel
    @1
    cA
    sdomdom
    a1i
    ss2rabi
    @3
    @22
    con0
    ssexg
    mpan
    @3
    cvv
    elong
    3syl
    mpbiri
    @3
    c0
    wceq
    #
    @4
    @0
    @25
    @4
    c0
    con0
    wcel
    0elon
    @3
    c0
    con0
    eleq1
    mpbiri
    @25
    wn
    #
    @2
    vx
    con0
    wrex
    #
    @0
    @26
    @3
    c0
    wne
    @27
    @3
    c0
    df-ne
    @2
    vx
    con0
    rabn0
    bitr3i
    @2
    @0
    vx
    con0
    @1
    cA
    csdm
    relsdom
    brrelex2i
    rexlimivw
    sylbi
    nsyl4
    pm2.61i
end
