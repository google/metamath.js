include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "word.mm"
include "ordon.mm"
include "tz7.5.mm"
include "mp3an1.mm"
include "wi.mm"
include "wel.mm"
include "ssel.mm"
include "imdistani.mm"
include "wn.mm"
include "wral.mm"
include "ontri1.mm"
include "syl6bir.mm"
include "ex.mm"
include "sylan9.mm"
include "com4r.mm"
include "imp31.mm"
include "ralimdva.mm"
include "disj.mm"
include "vex.mm"
include "elint2.mm"
include "3imtr4g.mm"
include "sylan2.mm"
include "exp32.mm"
include "com4l.mm"
include "imp32.mm"
include "ssrdv.mm"
include "intss1.mm"
include "ad2antrl.mm"
include "eqssd.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "com34.mm"
include "pm2.43d.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "anabsi5.mm"

theorem onint
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. A )

  proof
    cA
    con0
    wss
    #
    cA
    c0
    wne
    #
    cA
    cint
    #
    cA
    wcel
    #
    @0
    @1
    wa
    cA
    vx
    cv
    #
    cin
    c0
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    @3
    con0
    word
    @0
    @1
    @6
    ordon
    vx
    con0
    cA
    tz7.5
    mp3an1
    @0
    @5
    @3
    vx
    cA
    @0
    @4
    cA
    wcel
    #
    @5
    @3
    wi
    @0
    @7
    @5
    @7
    @3
    @0
    @7
    @5
    @7
    @3
    wi
    @0
    @7
    @5
    wa
    wa
    #
    @7
    @3
    @8
    @4
    @2
    cA
    @8
    @4
    @2
    @8
    vy
    @4
    @2
    @0
    @7
    @5
    vy
    vx
    wel
    #
    vy
    cv
    #
    @2
    wcel
    #
    wi
    @9
    @0
    @7
    @5
    @11
    @9
    @0
    @7
    @5
    @11
    wi
    #
    @0
    @7
    wa
    @9
    @0
    @4
    con0
    wcel
    #
    wa
    #
    @12
    @0
    @7
    @13
    cA
    con0
    @4
    ssel
    imdistani
    @9
    @14
    wa
    #
    vz
    vx
    wel
    wn
    #
    vz
    cA
    wral
    vy
    vz
    wel
    #
    vz
    cA
    wral
    @5
    @11
    @15
    @16
    @17
    vz
    cA
    @9
    @14
    vz
    cv
    #
    cA
    wcel
    #
    @16
    @17
    wi
    @14
    @19
    @16
    @9
    @17
    @0
    @19
    @18
    con0
    wcel
    #
    @13
    @16
    @9
    @17
    wi
    #
    wi
    #
    cA
    con0
    @18
    ssel
    @13
    @20
    @22
    @13
    @20
    wa
    @16
    @4
    @18
    wss
    @21
    @4
    @18
    ontri1
    @4
    @18
    @10
    ssel
    syl6bir
    ex
    sylan9
    com4r
    imp31
    ralimdva
    vz
    cA
    @4
    disj
    vz
    @10
    cA
    vy
    vex
    elint2
    3imtr4g
    sylan2
    exp32
    com4l
    imp32
    ssrdv
    @7
    @2
    @4
    wss
    @0
    @5
    @4
    cA
    intss1
    ad2antrl
    eqssd
    eleq1d
    biimpd
    exp32
    com34
    pm2.43d
    rexlimdv
    syl5
    anabsi5
end
