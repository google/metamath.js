include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "cv.mm"
include "ccrd.mm"
include "wceq.mm"
include "com.mm"
include "wss.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "cab.mm"
include "cint.mm"
include "alephcard.mm"
include "a1i.mm"
include "alephgeom.mm"
include "biimpi.mm"
include "alephord2i.mm"
include "elirr.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "con2i.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "fvex.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "sseq2.mm"
include "eqeq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "elab.mm"
include "syl3anbrc.mm"
include "wa.mm"
include "wi.mm"
include "wrex.mm"
include "cardalephex.mm"
include "biimpac.mm"
include "eleq1.mm"
include "alephord2.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "biimpcd.mm"
include "simpr.mm"
include "jcad.mm"
include "exp4c.mm"
include "com3r.mm"
include "imp4b.mm"
include "reximdv2.mm"
include "syl5.mm"
include "imp.mm"
include "dfrex2.mm"
include "sylib.mm"
include "nan.mm"
include "mpbir.mm"
include "ex.mm"
include "vex.mm"
include "df-3an.mm"
include "bitri.mm"
include "notbii.mm"
include "syl6ibr.mm"
include "cardon.mm"
include "mpbii.mm"
include "3ad2ant1.mm"
include "abssi.mm"
include "oneqmini.mm"
include "ax-mp.mm"
include "syl2anc.mm"

theorem alephval3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( A e. On -> ( aleph ` A ) = |^| { x | ( ( card ` x ) = x /\ _om C_ x /\ A. y e. A -. x = ( aleph ` y ) ) } )

  proof
    cA
    con0
    wcel
    #
    cA
    cale
    cfv
    #
    vx
    cv
    #
    ccrd
    cfv
    #
    @2
    wceq
    #
    com
    @2
    wss
    #
    @2
    vy
    cv
    #
    cale
    cfv
    #
    wceq
    #
    wn
    #
    vy
    cA
    wral
    #
    w3a
    #
    vx
    cab
    #
    wcel
    #
    vz
    cv
    #
    @12
    wcel
    #
    wn
    #
    vz
    @1
    wral
    #
    @1
    @12
    cint
    wceq
    #
    @0
    @1
    ccrd
    cfv
    #
    @1
    wceq
    #
    com
    @1
    wss
    #
    @1
    @7
    wceq
    #
    wn
    #
    vy
    cA
    wral
    #
    @13
    @20
    @0
    cA
    alephcard
    a1i
    @0
    @21
    cA
    alephgeom
    biimpi
    @0
    @23
    vy
    cA
    @0
    @6
    cA
    wcel
    #
    @7
    @1
    wcel
    #
    @23
    @6
    cA
    alephord2i
    @22
    @26
    @22
    @26
    @7
    @7
    wcel
    @7
    elirr
    @1
    @7
    @7
    eleq2
    mtbiri
    con2i
    syl6
    ralrimiv
    @11
    @20
    @21
    @24
    w3a
    vx
    @1
    cA
    cale
    fvex
    @2
    @1
    wceq
    #
    @4
    @20
    @5
    @21
    @10
    @24
    @27
    @3
    @19
    @2
    @1
    @2
    @1
    ccrd
    fveq2
    @27
    id
    eqeq12d
    @2
    @1
    com
    sseq2
    @27
    @9
    @23
    vy
    cA
    @27
    @8
    @22
    @2
    @1
    @7
    eqeq1
    notbid
    ralbidv
    3anbi123d
    elab
    syl3anbrc
    @0
    @16
    vz
    @1
    @0
    @14
    @1
    wcel
    #
    @14
    ccrd
    cfv
    #
    @14
    wceq
    #
    com
    @14
    wss
    #
    wa
    #
    @14
    @7
    wceq
    #
    wn
    #
    vy
    cA
    wral
    #
    wa
    #
    wn
    #
    @16
    @0
    @28
    @37
    @0
    @28
    wa
    #
    @37
    wi
    @38
    @32
    wa
    #
    @35
    wn
    #
    wi
    @39
    @33
    vy
    cA
    wrex
    #
    @40
    @38
    @32
    @41
    @32
    @33
    vy
    con0
    wrex
    #
    @38
    @41
    @31
    @30
    @42
    vy
    @14
    cardalephex
    biimpac
    @38
    @33
    @33
    vy
    con0
    cA
    @0
    @28
    @6
    con0
    wcel
    #
    @33
    @25
    @33
    wa
    #
    @28
    @43
    @0
    @33
    @44
    wi
    @28
    @43
    @0
    @33
    @44
    @28
    @43
    @0
    wa
    #
    @33
    wa
    #
    @25
    @33
    @46
    @28
    @25
    @33
    @28
    @26
    @45
    @25
    @14
    @7
    @1
    eleq1
    @45
    @25
    @26
    @6
    cA
    alephord2
    bicomd
    sylan9bbr
    biimpcd
    @46
    @33
    wi
    @28
    @45
    @33
    simpr
    a1i
    jcad
    exp4c
    com3r
    imp4b
    reximdv2
    syl5
    imp
    @33
    vy
    cA
    dfrex2
    sylib
    @38
    @32
    @35
    nan
    mpbir
    ex
    @15
    @36
    @15
    @30
    @31
    @35
    w3a
    #
    @36
    @11
    @47
    vx
    @14
    vz
    vex
    @2
    @14
    wceq
    #
    @4
    @30
    @5
    @31
    @10
    @35
    @48
    @3
    @29
    @2
    @14
    @2
    @14
    ccrd
    fveq2
    @48
    id
    eqeq12d
    @2
    @14
    com
    sseq2
    @48
    @9
    @34
    vy
    cA
    @48
    @8
    @33
    @2
    @14
    @7
    eqeq1
    notbid
    ralbidv
    3anbi123d
    elab
    @30
    @31
    @35
    df-3an
    bitri
    notbii
    syl6ibr
    ralrimiv
    @12
    con0
    wss
    @13
    @17
    wa
    @18
    wi
    @11
    vx
    con0
    @4
    @5
    @2
    con0
    wcel
    #
    @10
    @4
    @3
    con0
    wcel
    @49
    @2
    cardon
    @3
    @2
    con0
    eleq1
    mpbii
    3ad2ant1
    abssi
    vz
    @1
    @12
    oneqmini
    ax-mp
    syl2anc
end
