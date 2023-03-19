include "cv.mm"
include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wel.mm"
include "cin.mm"
include "wceq.mm"
include "wn.mm"
include "wrex.mm"
include "ssid.mm"
include "wi.mm"
include "simpr.mm"
include "a1i.mm"
include "df-ne.mm"
include "syl6ibr.mm"
include "pm3.2.mm"
include "mpsylsyld.mm"
include "wsbc.mm"
include "cvv.mm"
include "wcel.mm"
include "wal.mm"
include "vex.mm"
include "inex2.mm"
include "cep.mm"
include "wfr.mm"
include "wwe.mm"
include "inss2.mm"
include "word.mm"
include "simpl.mm"
include "ssel.mm"
include "syl2im.mm"
include "eloni.mm"
include "syl6.mm"
include "ordwe.mm"
include "wess.mm"
include "wefr.mm"
include "dfepfr.mm"
include "syl6ib.mm"
include "spsbc.mm"
include "onfrALTlem5.mm"
include "mpdd.mm"

theorem onfrALTlem3
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b

  disjoint a y
  disjoint x y
  disjoint a b
  disjoint b y
  disjoint b x
  assert |- ( ( a C_ On /\ a =/= (/) ) -> ( ( x e. a /\ -. ( a i^i x ) = (/) ) -> E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ) )

  proof
    va
    cv
    #
    con0
    wss
    #
    @0
    c0
    wne
    #
    wa
    #
    vx
    va
    wel
    #
    @0
    vx
    cv
    #
    cin
    #
    c0
    wceq
    wn
    #
    wa
    #
    @6
    @6
    wss
    #
    @6
    c0
    wne
    #
    wa
    #
    @6
    vy
    cv
    #
    cin
    c0
    wceq
    vy
    @6
    wrex
    #
    @9
    @3
    @8
    @10
    @11
    @6
    ssid
    @3
    @8
    @7
    @10
    @8
    @7
    wi
    @3
    @4
    @7
    simpr
    a1i
    @6
    c0
    df-ne
    syl6ibr
    @9
    @10
    pm3.2
    mpsylsyld
    @3
    @8
    vb
    cv
    #
    @6
    wss
    @14
    c0
    wne
    wa
    @14
    @12
    cin
    c0
    wceq
    vy
    @14
    wrex
    wi
    #
    vb
    @6
    wsbc
    #
    @11
    @13
    wi
    @6
    cvv
    wcel
    @3
    @8
    @15
    vb
    wal
    #
    @16
    @5
    @0
    vx
    vex
    inex2
    @3
    @8
    @6
    cep
    wfr
    #
    @17
    @3
    @8
    @6
    cep
    wwe
    #
    @18
    @6
    @5
    wss
    @3
    @8
    @5
    cep
    wwe
    #
    @19
    @0
    @5
    inss2
    @3
    @8
    @5
    word
    #
    @20
    @3
    @8
    @5
    con0
    wcel
    #
    @21
    @3
    @1
    @8
    @4
    @22
    @1
    @2
    simpl
    @4
    @7
    simpl
    @0
    con0
    @5
    ssel
    syl2im
    @5
    eloni
    syl6
    @5
    ordwe
    syl6
    @6
    @5
    cep
    wess
    mpsylsyld
    @6
    cep
    wefr
    syl6
    vb
    vy
    @6
    dfepfr
    syl6ib
    @15
    vb
    @6
    cvv
    spsbc
    mpsylsyld
    vx
    vy
    va
    vb
    onfrALTlem5
    syl6ib
    mpdd
end
