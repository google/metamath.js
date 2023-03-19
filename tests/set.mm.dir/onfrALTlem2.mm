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
include "wex.mm"
include "wrex.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "simpr.mm"
include "2a1i.mm"
include "inss2.mm"
include "sseli.mm"
include "syl8.mm"
include "inss1.mm"
include "wtr.mm"
include "word.mm"
include "simpl.mm"
include "ssel.mm"
include "syl2im.mm"
include "eloni.mm"
include "syl6.mm"
include "ordtr.mm"
include "simpll.mm"
include "trel.mm"
include "expcomd.mm"
include "ee233.mm"
include "elin.mm"
include "simplbi2.mm"
include "ee33.mm"
include "simplbi2com.mm"
include "exp4a.mm"
include "ggen31.mm"
include "dfss2.mm"
include "biimpri.mm"
include "sseq0.mm"
include "ex.mm"
include "pm3.21.mm"
include "alrimdv.mm"
include "onfrALTlem3.mm"
include "df-rex.mm"
include "syl6ib.mm"
include "exim.mm"
include "syl6c.mm"
include "syl6ibr.mm"

theorem onfrALTlem2
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vz: setvar z

  disjoint a y
  disjoint x y
  disjoint a z
  disjoint y z
  disjoint x z
  assert |- ( ( a C_ On /\ a =/= (/) ) -> ( ( x e. a /\ -. ( a i^i x ) = (/) ) -> E. y e. a ( a i^i y ) = (/) ) )

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
    vy
    va
    wel
    #
    @0
    vy
    cv
    #
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
    @3
    @8
    @10
    @6
    wcel
    #
    @6
    @10
    cin
    #
    c0
    wceq
    #
    wa
    #
    @13
    wi
    #
    vy
    wal
    @18
    vy
    wex
    #
    @14
    @3
    @8
    @19
    vy
    @3
    @8
    @18
    @12
    @9
    @13
    @3
    @8
    @18
    @11
    @16
    wss
    #
    @17
    @12
    @3
    @8
    @18
    vz
    cv
    #
    @11
    wcel
    #
    @22
    @16
    wcel
    #
    wi
    #
    vz
    wal
    #
    @21
    @3
    @8
    @18
    @25
    vz
    @3
    @8
    @18
    @23
    @24
    @3
    @8
    @18
    @23
    wa
    #
    vz
    vy
    wel
    #
    @22
    @6
    wcel
    #
    @24
    @3
    @8
    @27
    @23
    @28
    @27
    @23
    wi
    @3
    @8
    @18
    @23
    simpr
    2a1i
    #
    @11
    @10
    @22
    @0
    @10
    inss2
    sseli
    syl8
    #
    @3
    @8
    @27
    vz
    va
    wel
    #
    vz
    vx
    wel
    #
    @29
    @3
    @8
    @27
    @23
    @32
    @30
    @11
    @0
    @22
    @0
    @10
    inss1
    sseli
    syl8
    @3
    @8
    @5
    wtr
    #
    @27
    vy
    vx
    wel
    #
    @28
    @33
    @3
    @8
    @5
    word
    #
    @34
    @3
    @8
    @5
    con0
    wcel
    #
    @36
    @3
    @1
    @8
    @4
    @37
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
    ordtr
    syl6
    @3
    @8
    @27
    @15
    @35
    @27
    @15
    wi
    @3
    @8
    @15
    @17
    @23
    simpll
    2a1i
    @6
    @5
    @10
    @0
    @5
    inss2
    sseli
    syl8
    @31
    @34
    @28
    @35
    @33
    @5
    @22
    @10
    trel
    expcomd
    ee233
    @29
    @32
    @33
    @22
    @0
    @5
    elin
    simplbi2
    ee33
    @24
    @29
    @28
    @22
    @6
    @10
    elin
    simplbi2com
    ee33
    exp4a
    ggen31
    @21
    @26
    vz
    @11
    @16
    dfss2
    biimpri
    syl8
    @18
    @17
    wi
    @3
    @8
    @15
    @17
    simpr
    2a1i
    @21
    @17
    @12
    @11
    @16
    sseq0
    ex
    ee33
    @3
    @8
    @18
    @15
    @9
    @18
    @15
    wi
    @3
    @8
    @15
    @17
    simpl
    2a1i
    @6
    @0
    @10
    @0
    @5
    inss1
    sseli
    syl8
    @12
    @9
    pm3.21
    ee33
    alrimdv
    @3
    @8
    @17
    vy
    @6
    wrex
    @20
    vx
    vy
    va
    onfrALTlem3
    @17
    vy
    @6
    df-rex
    syl6ib
    @18
    @13
    vy
    exim
    syl6c
    @12
    vy
    @0
    df-rex
    syl6ibr
end
