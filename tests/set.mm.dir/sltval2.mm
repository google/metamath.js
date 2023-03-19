include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c1o.mm"
include "c0.mm"
include "cop.mm"
include "c2o.mm"
include "ctp.mm"
include "con0.mm"
include "wrex.mm"
include "wne.mm"
include "crab.mm"
include "cint.mm"
include "sltval.mm"
include "cvv.mm"
include "w3o.mm"
include "fvex.mm"
include "brtp.mm"
include "1n0.mm"
include "neii.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "fvprc.mm"
include "nsyl2.mm"
include "adantr.mm"
include "2on0.mm"
include "adantl.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "onintrab.mm"
include "sylib.mm"
include "wn.mm"
include "onelon.mm"
include "expcom.mm"
include "syl5.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "onnminsb.mm"
include "com12.mm"
include "syldc.mm"
include "df-ne.mm"
include "con2bii.mm"
include "syl6ibr.mm"
include "ralrimiv.mm"
include "jca.mm"
include "ex.mm"
include "impac.mm"
include "anass.mm"
include "raleq.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl.mm"
include "wi.mm"
include "eqeq12.mm"
include "csuc.mm"
include "wb.mm"
include "1on.mm"
include "0elon.mm"
include "suc11.mm"
include "necon3bid.mm"
include "mp2an.mm"
include "mpbir.mm"
include "df-2o.mm"
include "df-1o.mm"
include "eqeq12i.mm"
include "nemtbir.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "nesymi.mm"
include "3imtr4i.mm"
include "elrab.mm"
include "biimpri.mm"
include "adantlr.mm"
include "wss.mm"
include "ssrab2.mm"
include "ne0i.mm"
include "onint.mm"
include "sylancr.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfne.mm"
include "elrabf.mm"
include "simprbi.mm"
include "eqeq12d.mm"
include "rspccv.mm"
include "ad2antlr.mm"
include "mtod.mm"
include "simpll.mm"
include "oninton.mm"
include "ontri1.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "intss1.mm"
include "eqssd.mm"
include "syldan.mm"
include "sylan2.mm"
include "fveq2d.mm"
include "biimpd.mm"
include "pm2.43d.mm"
include "expimpd.mm"
include "rexlimiv.mm"
include "impbid1.mm"
include "bitr4d.mm"

theorem sltval2
  let cA: class A
  let cB: class B
  let va: setvar a
  let vx: setvar x
  let vy: setvar y

  disjoint A a
  disjoint B a
  disjoint A x
  disjoint A y
  disjoint a x
  disjoint a y
  disjoint x y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. No /\ B e. No ) -> ( A <s B <-> ( A ` |^| { a e. On | ( A ` a ) =/= ( B ` a ) } ) { <. 1o , (/) >. , <. 1o , 2o >. , <. (/) , 2o >. } ( B ` |^| { a e. On | ( A ` a ) =/= ( B ` a ) } ) ) )

  proof
    cA
    csur
    wcel
    cB
    csur
    wcel
    wa
    #
    cA
    cB
    cslt
    wbr
    vy
    cv
    #
    cA
    cfv
    #
    @1
    cB
    cfv
    #
    wceq
    #
    vy
    vx
    cv
    #
    wral
    #
    @5
    cA
    cfv
    #
    @5
    cB
    cfv
    #
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    #
    wbr
    #
    wa
    #
    vx
    con0
    wrex
    #
    va
    cv
    #
    cA
    cfv
    #
    @13
    cB
    cfv
    #
    wne
    #
    va
    con0
    crab
    #
    cint
    #
    cA
    cfv
    #
    @18
    cB
    cfv
    #
    @9
    wbr
    #
    vx
    vy
    cA
    cB
    sltval
    @0
    @21
    @12
    @0
    @21
    @12
    @0
    @21
    wa
    #
    @18
    con0
    wcel
    #
    @4
    vy
    @18
    wral
    #
    @21
    wa
    #
    wa
    #
    @12
    @22
    @23
    @24
    wa
    #
    @21
    wa
    @26
    @0
    @21
    @27
    @0
    @21
    @27
    @22
    @23
    @24
    @21
    @23
    @0
    @21
    @18
    cvv
    wcel
    #
    @23
    @21
    @19
    c1o
    wceq
    #
    @20
    c0
    wceq
    #
    wa
    #
    @29
    @20
    c2o
    wceq
    #
    wa
    #
    @19
    c0
    wceq
    #
    @32
    wa
    #
    w3o
    @28
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @19
    @20
    @18
    cA
    fvex
    @18
    cB
    fvex
    brtp
    @31
    @28
    @33
    @35
    @29
    @28
    @30
    @29
    @34
    @28
    @29
    @34
    c1o
    c0
    wceq
    #
    c1o
    c0
    1n0
    neii
    #
    @19
    c1o
    c0
    eqeq1
    mtbiri
    @18
    cA
    fvprc
    nsyl2
    #
    adantr
    @29
    @28
    @32
    @38
    adantr
    @32
    @28
    @34
    @32
    @30
    @28
    @32
    @30
    c2o
    c0
    wceq
    c2o
    c0
    2on0
    neii
    @20
    c2o
    c0
    eqeq1
    mtbiri
    @18
    cB
    fvprc
    nsyl2
    adantl
    3jaoi
    sylbi
    @16
    va
    onintrab
    sylib
    adantl
    #
    @22
    @4
    vy
    @18
    @22
    @1
    @18
    wcel
    #
    @2
    @3
    wne
    #
    wn
    #
    @4
    @40
    @22
    @1
    con0
    wcel
    #
    @42
    @22
    @23
    @40
    @43
    @39
    @23
    @40
    @43
    @18
    @1
    onelon
    expcom
    syl5
    @43
    @40
    @42
    @16
    @41
    va
    @1
    @13
    @1
    wceq
    @14
    @2
    @15
    @3
    @13
    @1
    cA
    fveq2
    @13
    @1
    cB
    fveq2
    neeq12d
    onnminsb
    com12
    syldc
    @41
    @4
    @2
    @3
    df-ne
    con2bii
    syl6ibr
    ralrimiv
    jca
    ex
    impac
    @23
    @24
    @21
    anass
    sylib
    @11
    @25
    vx
    @18
    con0
    @5
    @18
    wceq
    #
    @6
    @24
    @10
    @21
    @4
    vy
    @5
    @18
    raleq
    @44
    @7
    @19
    @8
    @20
    @9
    @5
    @18
    cA
    fveq2
    @5
    @18
    cB
    fveq2
    breq12d
    anbi12d
    rspcev
    syl
    ex
    @11
    @21
    vx
    con0
    @5
    con0
    wcel
    #
    @6
    @10
    @21
    @45
    @6
    wa
    #
    @10
    @21
    @46
    @10
    @10
    @21
    wi
    @46
    @10
    wa
    #
    @10
    @21
    @47
    @7
    @19
    @8
    @20
    @9
    @47
    @5
    @18
    cA
    @10
    @46
    @7
    @8
    wne
    #
    @44
    @7
    c1o
    wceq
    #
    @8
    c0
    wceq
    wa
    #
    @49
    @8
    c2o
    wceq
    #
    wa
    #
    @7
    c0
    wceq
    @51
    wa
    #
    w3o
    @7
    @8
    wceq
    #
    wn
    #
    @10
    @48
    @50
    @55
    @52
    @53
    @50
    @54
    @36
    @37
    @7
    c1o
    @8
    c0
    eqeq12
    mtbiri
    @52
    @54
    c2o
    c1o
    wceq
    #
    @56
    c1o
    csuc
    #
    c0
    csuc
    #
    @57
    @58
    wne
    #
    c1o
    c0
    wne
    #
    1n0
    c1o
    con0
    wcel
    #
    c0
    con0
    wcel
    #
    @59
    @60
    wb
    1on
    0elon
    @61
    @62
    wa
    @57
    @58
    c1o
    c0
    c1o
    c0
    suc11
    necon3bid
    mp2an
    mpbir
    c2o
    @57
    c1o
    @58
    df-2o
    df-1o
    eqeq12i
    nemtbir
    @52
    @54
    c1o
    c2o
    wceq
    @56
    @7
    c1o
    @8
    c2o
    eqeq12
    c1o
    c2o
    eqcom
    syl6bb
    mtbiri
    @53
    @54
    c0
    c2o
    wceq
    c2o
    c0
    2on0
    nesymi
    @7
    c0
    @8
    c2o
    eqeq12
    mtbiri
    3jaoi
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @7
    @8
    @5
    cA
    fvex
    @5
    cB
    fvex
    brtp
    @7
    @8
    df-ne
    3imtr4i
    @46
    @48
    @5
    @17
    wcel
    #
    @44
    @45
    @48
    @63
    @6
    @63
    @45
    @48
    wa
    @16
    @48
    va
    @5
    con0
    @13
    @5
    wceq
    @14
    @7
    @15
    @8
    @13
    @5
    cA
    fveq2
    @13
    @5
    cB
    fveq2
    neeq12d
    elrab
    biimpri
    adantlr
    @46
    @63
    wa
    #
    @5
    @18
    @64
    @5
    @18
    wss
    #
    @18
    @5
    wcel
    #
    wn
    #
    @64
    @66
    @19
    @20
    wceq
    #
    @64
    @19
    @20
    wne
    #
    @68
    wn
    @64
    @18
    @17
    wcel
    #
    @69
    @64
    @17
    con0
    wss
    #
    @17
    c0
    wne
    #
    @70
    @16
    va
    con0
    ssrab2
    #
    @63
    @72
    @46
    @17
    @5
    ne0i
    #
    adantl
    @17
    onint
    sylancr
    @70
    @23
    @69
    @16
    @69
    va
    @18
    con0
    va
    @17
    @16
    va
    con0
    nfrab1
    nfint
    #
    va
    con0
    nfcv
    va
    @19
    @20
    va
    @18
    cA
    va
    cA
    nfcv
    @75
    nffv
    va
    @18
    cB
    va
    cB
    nfcv
    @75
    nffv
    nfne
    @13
    @18
    wceq
    @14
    @19
    @15
    @20
    @13
    @18
    cA
    fveq2
    @13
    @18
    cB
    fveq2
    neeq12d
    elrabf
    simprbi
    syl
    @19
    @20
    df-ne
    sylib
    @6
    @66
    @68
    wi
    @45
    @63
    @4
    @68
    vy
    @18
    @5
    @1
    @18
    wceq
    @2
    @19
    @3
    @20
    @1
    @18
    cA
    fveq2
    @1
    @18
    cB
    fveq2
    eqeq12d
    rspccv
    ad2antlr
    mtod
    @64
    @45
    @23
    @65
    @67
    wb
    @45
    @6
    @63
    simpll
    @63
    @23
    @46
    @63
    @71
    @72
    @23
    @73
    @74
    @17
    oninton
    sylancr
    adantl
    @5
    @18
    ontri1
    syl2anc
    mpbird
    @63
    @18
    @5
    wss
    @46
    @5
    @17
    intss1
    adantl
    eqssd
    syldan
    sylan2
    #
    fveq2d
    @47
    @5
    @18
    cB
    @76
    fveq2d
    breq12d
    biimpd
    ex
    pm2.43d
    expimpd
    rexlimiv
    impbid1
    bitr4d
end
