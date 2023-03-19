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
include "cfv.mm"
include "wceq.mm"
include "cep.mm"
include "wrex.mm"
include "copab.mm"
include "cdm.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "w3a.mm"
include "cdif.mm"
include "wwe.mm"
include "coi.mm"
include "eqid.mm"
include "hartogslem2.mm"
include "elong.mm"
include "syl.mm"
include "mpbiri.mm"

theorem hartogs
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vg: setvar g
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A g
  disjoint A r
  disjoint A y
  disjoint A z
  disjoint V r
  disjoint V y
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
    @4
    @5
    wb
    vx
    vy
    vz
    vw
    vt
    cA
    vs
    cv
    vw
    cv
    #
    vg
    cv
    #
    cfv
    wceq
    vt
    cv
    @8
    @22
    cfv
    wceq
    wa
    @21
    @8
    cep
    wbr
    wa
    vz
    @7
    wrex
    vw
    @7
    wrex
    vs
    vt
    copab
    #
    vg
    vr
    cv
    #
    cdm
    #
    cA
    wss
    cid
    @25
    cres
    @24
    wss
    @24
    @25
    @25
    cxp
    wss
    w3a
    @25
    @24
    cid
    cdif
    #
    wwe
    wa
    @7
    @25
    @26
    coi
    cdm
    wceq
    wa
    vr
    vy
    copab
    #
    cV
    vs
    vr
    @27
    eqid
    @23
    eqid
    hartogslem2
    @3
    cvv
    elong
    syl
    mpbiri
end
