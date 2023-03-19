include "cv.mm"
include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wcel.mm"
include "cin.mm"
include "wceq.mm"
include "wn.mm"
include "wrex.mm"
include "wi.mm"
include "wsbc.mm"
include "cvv.mm"
include "wal.mm"
include "vex.mm"
include "inss2.mm"
include "ssexi.mm"
include "cep.mm"
include "wfr.mm"
include "wwe.mm"
include "word.mm"
include "idn2.mm"
include "simpl.mm"
include "e2.mm"
include "idn1.mm"
include "e1a.mm"
include "ssel.mm"
include "com12.mm"
include "e21.mm"
include "eloni.mm"
include "ordwe.mm"
include "wess.mm"
include "e20.mm"
include "wefr.mm"
include "dfepfr.mm"
include "biimpi.mm"
include "spsbc.mm"
include "e02.mm"
include "onfrALTlem5.mm"
include "e2bi.mm"
include "ssid.mm"
include "simpr.mm"
include "df-ne.mm"
include "biimpri.mm"
include "pm3.2.mm"
include "id.mm"
include "e22.mm"

theorem onfrALTlem3VD
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vb: setvar b

  disjoint a y
  disjoint x y
  disjoint a b
  disjoint b y
  disjoint b x
  assert |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\ -. ( a i^i x ) = (/) ) ->. E. y e. ( a i^i x ) ( ( a i^i x ) i^i y ) = (/) ).

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
    cv
    #
    @0
    wcel
    #
    @0
    @4
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
    wi
    #
    @11
    @13
    @3
    @8
    vb
    cv
    #
    @6
    wss
    @15
    c0
    wne
    wa
    @15
    @12
    cin
    c0
    wceq
    vy
    @15
    wrex
    wi
    #
    vb
    @6
    wsbc
    #
    @14
    @6
    cvv
    wcel
    @3
    @8
    @16
    vb
    wal
    #
    @17
    @6
    @4
    vx
    vex
    @0
    @4
    inss2
    #
    ssexi
    @3
    @8
    @6
    cep
    wfr
    #
    @18
    @3
    @8
    @6
    cep
    wwe
    #
    @20
    @3
    @8
    @4
    cep
    wwe
    #
    @6
    @4
    wss
    #
    @21
    @3
    @8
    @4
    word
    #
    @22
    @3
    @8
    @4
    con0
    wcel
    #
    @24
    @3
    @8
    @5
    @1
    @25
    @3
    @8
    @8
    @5
    @3
    @8
    idn2
    #
    @5
    @7
    simpl
    e2
    @3
    @3
    @1
    @3
    idn1
    @1
    @2
    simpl
    e1a
    @1
    @5
    @25
    @0
    con0
    @4
    ssel
    com12
    e21
    @4
    eloni
    e2
    @4
    ordwe
    e2
    @19
    @23
    @22
    @21
    @6
    @4
    cep
    wess
    com12
    e20
    @6
    cep
    wefr
    e2
    @20
    @18
    vb
    vy
    @6
    dfepfr
    biimpi
    e2
    @16
    vb
    @6
    cvv
    spsbc
    e02
    vx
    vy
    va
    vb
    onfrALTlem5
    e2bi
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
    @3
    @8
    @8
    @7
    @26
    @5
    @7
    simpr
    e2
    @10
    @7
    @6
    c0
    df-ne
    biimpri
    e2
    @9
    @10
    pm3.2
    e02
    @14
    id
    e22
end
