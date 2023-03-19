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
include "wex.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "idn3.mm"
include "simpr.mm"
include "e3.mm"
include "inss2.mm"
include "sseli.mm"
include "inss1.mm"
include "wtr.mm"
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
include "ordtr.mm"
include "simpll.mm"
include "trel.mm"
include "expcomd.mm"
include "e233.mm"
include "elin.mm"
include "simplbi2.mm"
include "e33.mm"
include "simplbi2com.mm"
include "in3an.mm"
include "gen31.mm"
include "dfss2.mm"
include "biimpri.mm"
include "sseq0.mm"
include "ex.mm"
include "pm3.21.mm"
include "in3.mm"
include "gen21.mm"
include "exim.mm"
include "onfrALTlem3VD.mm"
include "df-rex.mm"
include "biimpi.mm"
include "id.mm"
include "e22.mm"

theorem onfrALTlem2VD
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vz: setvar z

  disjoint a y
  disjoint x y
  disjoint a z
  disjoint y z
  disjoint x z
  assert |- (. ( a C_ On /\ a =/= (/) ) ,. ( x e. a /\ -. ( a i^i x ) = (/) ) ->. E. y e. a ( a i^i y ) = (/) ).

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
    vy
    cv
    #
    @0
    wcel
    #
    @0
    @9
    cin
    #
    c0
    wceq
    #
    wa
    #
    vy
    wex
    #
    @12
    vy
    @0
    wrex
    #
    @3
    @8
    @9
    @6
    wcel
    #
    @6
    @9
    cin
    #
    c0
    wceq
    #
    wa
    #
    vy
    wex
    #
    @14
    wi
    #
    @20
    @14
    @3
    @8
    @19
    @13
    wi
    #
    vy
    wal
    @21
    @3
    @8
    @22
    vy
    @3
    @8
    @19
    @13
    @3
    @8
    @19
    @12
    @10
    @13
    @3
    @8
    @19
    @11
    @17
    wss
    #
    @18
    @12
    @3
    @8
    @19
    vz
    cv
    #
    @11
    wcel
    #
    @24
    @17
    wcel
    #
    wi
    #
    vz
    wal
    #
    @23
    @3
    @8
    @19
    @27
    vz
    @3
    @8
    @19
    @25
    @26
    @3
    @8
    @19
    @25
    wa
    #
    @24
    @9
    wcel
    #
    @24
    @6
    wcel
    #
    @26
    @3
    @8
    @29
    @25
    @30
    @3
    @8
    @29
    @29
    @25
    @3
    @8
    @29
    idn3
    #
    @19
    @25
    simpr
    e3
    #
    @11
    @9
    @24
    @0
    @9
    inss2
    sseli
    e3
    #
    @3
    @8
    @29
    @24
    @0
    wcel
    #
    @24
    @4
    wcel
    #
    @31
    @3
    @8
    @29
    @25
    @35
    @33
    @11
    @0
    @24
    @0
    @9
    inss1
    sseli
    e3
    @3
    @8
    @4
    wtr
    #
    @29
    @9
    @4
    wcel
    #
    @30
    @36
    @3
    @8
    @4
    word
    #
    @37
    @3
    @8
    @4
    con0
    wcel
    #
    @39
    @3
    @8
    @5
    @1
    @40
    @3
    @8
    @8
    @5
    @3
    @8
    idn2
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
    @40
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
    ordtr
    e2
    @3
    @8
    @29
    @16
    @38
    @3
    @8
    @29
    @29
    @16
    @32
    @16
    @18
    @25
    simpll
    e3
    @6
    @4
    @9
    @0
    @4
    inss2
    sseli
    e3
    @34
    @37
    @30
    @38
    @36
    @4
    @24
    @9
    trel
    expcomd
    e233
    @31
    @35
    @36
    @24
    @0
    @4
    elin
    simplbi2
    e33
    @26
    @31
    @30
    @24
    @6
    @9
    elin
    simplbi2com
    e33
    in3an
    gen31
    @23
    @28
    vz
    @11
    @17
    dfss2
    biimpri
    e3
    @3
    @8
    @19
    @19
    @18
    @3
    @8
    @19
    idn3
    #
    @16
    @18
    simpr
    e3
    @23
    @18
    @12
    @11
    @17
    sseq0
    ex
    e33
    @3
    @8
    @19
    @16
    @10
    @3
    @8
    @19
    @19
    @16
    @41
    @16
    @18
    simpl
    e3
    @6
    @0
    @9
    @0
    @4
    inss1
    sseli
    e3
    @12
    @10
    pm3.21
    e33
    in3
    gen21
    @19
    @13
    vy
    exim
    e2
    @3
    @8
    @18
    vy
    @6
    wrex
    #
    @20
    vx
    vy
    va
    onfrALTlem3VD
    @42
    @20
    @18
    vy
    @6
    df-rex
    biimpi
    e2
    @21
    id
    e22
    @15
    @14
    @12
    vy
    @0
    df-rex
    biimpri
    e2
end
