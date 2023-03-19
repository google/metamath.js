include "com.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cuni.mm"
include "csuc.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wss.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "adantr.mm"
include "adantl.mm"
include "unssd.mm"
include "inss2.mm"
include "unfi.mm"
include "syl2an.mm"
include "nnunifi.mm"
include "syl2anc.mm"
include "peano2.mm"
include "syl.mm"
include "cv.mm"
include "c0.mm"
include "ineq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "in0.mm"
include "eqtr4i.mm"
include "2a1i.mm"
include "w3a.mm"
include "csn.mm"
include "coa.mm"
include "co.mm"
include "simp13.mm"
include "3simpa.mm"
include "ackbij1lem2.mm"
include "3ad2ant2.mm"
include "ackbij1lem4.mm"
include "simprl.mm"
include "ackbij1lem11.mm"
include "sylancl.mm"
include "incom.mm"
include "word.mm"
include "nnord.mm"
include "orddisj.mm"
include "ssdisj.mm"
include "sylancr.mm"
include "syl5eq.mm"
include "ackbij1lem9.mm"
include "syl3anc.mm"
include "3ad2ant1.mm"
include "eqtrd.mm"
include "syl3an1.mm"
include "3ad2ant3.mm"
include "simprr.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "ackbij1lem10.mm"
include "ffvelrni.mm"
include "nnacan.mm"
include "3adant3.mm"
include "mpbid.mm"
include "uneq2.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "3adant1.mm"
include "embantd.mm"
include "3exp.mm"
include "wn.mm"
include "eqcomd.mm"
include "simp12r.mm"
include "simp12l.mm"
include "simp11.mm"
include "simp3.mm"
include "simp2.mm"
include "ackbij1lem15.mm"
include "syl23anc.mm"
include "pm2.21dd.mm"
include "pm2.61d.mm"
include "ackbij1lem1.mm"
include "biimpd.mm"
include "mpd.mm"
include "biimprd.mm"
include "com34.mm"
include "a2d.mm"
include "finds.mm"
include "mpcom.mm"
include "con0.mm"
include "omsson.mm"
include "syl6ss.mm"
include "onsucuni.mm"
include "unssad.mm"
include "df-ss.mm"
include "sylib.mm"
include "unssbd.mm"
include "3imtr3d.mm"

theorem ackbij1lem16
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  assert |- ( ( A e. ( ~P _om i^i Fin ) /\ B e. ( ~P _om i^i Fin ) ) -> ( ( F ` A ) = ( F ` B ) -> A = B ) )

  proof
    cA
    com
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cA
    cA
    cB
    cun
    #
    cuni
    #
    csuc
    #
    cin
    #
    cF
    cfv
    #
    cB
    @7
    cin
    #
    cF
    cfv
    #
    wceq
    #
    @8
    @10
    wceq
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    wceq
    cA
    cB
    wceq
    @7
    com
    wcel
    #
    @4
    @12
    @13
    wi
    #
    @4
    @6
    com
    wcel
    #
    @16
    @4
    @5
    com
    wss
    @5
    cfn
    wcel
    #
    @18
    @4
    cA
    cB
    com
    @2
    cA
    com
    wss
    @3
    @2
    cA
    com
    @1
    @0
    cA
    @0
    cfn
    inss1
    #
    sseli
    elpwid
    adantr
    @3
    cB
    com
    wss
    @2
    @3
    cB
    com
    @1
    @0
    cB
    @20
    sseli
    elpwid
    adantl
    unssd
    #
    @2
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    @19
    @3
    @1
    cfn
    cA
    @0
    cfn
    inss2
    #
    sseli
    @1
    cfn
    cB
    @22
    sseli
    cA
    cB
    unfi
    syl2an
    @5
    nnunifi
    syl2anc
    @6
    peano2
    syl
    @4
    cA
    va
    cv
    #
    cin
    #
    cF
    cfv
    #
    cB
    @23
    cin
    #
    cF
    cfv
    #
    wceq
    #
    @24
    @26
    wceq
    #
    wi
    #
    wi
    @4
    cA
    c0
    cin
    #
    cF
    cfv
    #
    cB
    c0
    cin
    #
    cF
    cfv
    #
    wceq
    #
    @31
    @33
    wceq
    #
    wi
    #
    wi
    @4
    cA
    vb
    cv
    #
    cin
    #
    cF
    cfv
    #
    cB
    @38
    cin
    #
    cF
    cfv
    #
    wceq
    #
    @39
    @41
    wceq
    #
    wi
    #
    wi
    @4
    cA
    @38
    csuc
    #
    cin
    #
    cF
    cfv
    #
    cB
    @46
    cin
    #
    cF
    cfv
    #
    wceq
    #
    @47
    @49
    wceq
    #
    wi
    #
    wi
    @4
    @17
    wi
    va
    vb
    @7
    @23
    c0
    wceq
    #
    @30
    @37
    @4
    @54
    @28
    @35
    @29
    @36
    @54
    @25
    @32
    @27
    @34
    @54
    @24
    @31
    cF
    @23
    c0
    cA
    ineq2
    #
    fveq2d
    @54
    @26
    @33
    cF
    @23
    c0
    cB
    ineq2
    #
    fveq2d
    eqeq12d
    @54
    @24
    @31
    @26
    @33
    @55
    @56
    eqeq12d
    imbi12d
    imbi2d
    va
    vb
    weq
    #
    @30
    @45
    @4
    @57
    @28
    @43
    @29
    @44
    @57
    @25
    @40
    @27
    @42
    @57
    @24
    @39
    cF
    @23
    @38
    cA
    ineq2
    #
    fveq2d
    @57
    @26
    @41
    cF
    @23
    @38
    cB
    ineq2
    #
    fveq2d
    eqeq12d
    @57
    @24
    @39
    @26
    @41
    @58
    @59
    eqeq12d
    imbi12d
    imbi2d
    @23
    @46
    wceq
    #
    @30
    @53
    @4
    @60
    @28
    @51
    @29
    @52
    @60
    @25
    @48
    @27
    @50
    @60
    @24
    @47
    cF
    @23
    @46
    cA
    ineq2
    #
    fveq2d
    @60
    @26
    @49
    cF
    @23
    @46
    cB
    ineq2
    #
    fveq2d
    eqeq12d
    @60
    @24
    @47
    @26
    @49
    @61
    @62
    eqeq12d
    imbi12d
    imbi2d
    @23
    @7
    wceq
    #
    @30
    @17
    @4
    @63
    @28
    @12
    @29
    @13
    @63
    @25
    @9
    @27
    @11
    @63
    @24
    @8
    cF
    @23
    @7
    cA
    ineq2
    #
    fveq2d
    @63
    @26
    @10
    cF
    @23
    @7
    cB
    ineq2
    #
    fveq2d
    eqeq12d
    @63
    @24
    @8
    @26
    @10
    @64
    @65
    eqeq12d
    imbi12d
    imbi2d
    @36
    @4
    @35
    @31
    c0
    @33
    cA
    in0
    cB
    in0
    eqtr4i
    2a1i
    @38
    com
    wcel
    #
    @4
    @45
    @53
    @66
    @4
    @51
    @45
    @52
    @66
    @4
    @51
    @45
    @52
    wi
    #
    @66
    @4
    @51
    w3a
    #
    @38
    cB
    wcel
    #
    @67
    @68
    @38
    cA
    wcel
    #
    @69
    @67
    wi
    @68
    @70
    @69
    @67
    @68
    @70
    @69
    w3a
    #
    @43
    @44
    @52
    @71
    @38
    csn
    #
    cF
    cfv
    #
    @40
    coa
    co
    #
    @73
    @42
    coa
    co
    #
    wceq
    #
    @43
    @71
    @48
    @50
    @74
    @75
    @66
    @4
    @51
    @70
    @69
    simp13
    @68
    @66
    @4
    wa
    #
    @70
    @69
    @48
    @74
    wceq
    @66
    @4
    @51
    3simpa
    #
    @77
    @70
    @69
    w3a
    #
    @48
    @72
    @39
    cun
    #
    cF
    cfv
    #
    @74
    @70
    @77
    @48
    @81
    wceq
    @69
    @70
    @47
    @80
    cF
    @38
    cA
    ackbij1lem2
    #
    fveq2d
    3ad2ant2
    @77
    @70
    @81
    @74
    wceq
    #
    @69
    @77
    @72
    @1
    wcel
    #
    @39
    @1
    wcel
    #
    @72
    @39
    cin
    #
    c0
    wceq
    @83
    @66
    @84
    @4
    @38
    ackbij1lem4
    adantr
    #
    @77
    @2
    @39
    cA
    wss
    @85
    @66
    @2
    @3
    simprl
    cA
    @38
    inss1
    vx
    vy
    cA
    @39
    cF
    ackbij.f
    ackbij1lem11
    sylancl
    #
    @77
    @86
    @39
    @72
    cin
    #
    c0
    @72
    @39
    incom
    @77
    @39
    @38
    wss
    @38
    @72
    cin
    c0
    wceq
    #
    @89
    c0
    wceq
    cA
    @38
    inss2
    @66
    @90
    @4
    @66
    @38
    word
    @90
    @38
    nnord
    @38
    orddisj
    syl
    adantr
    #
    @39
    @38
    @72
    ssdisj
    sylancr
    syl5eq
    vx
    vy
    @72
    @39
    cF
    ackbij.f
    ackbij1lem9
    syl3anc
    3ad2ant1
    eqtrd
    syl3an1
    @68
    @77
    @70
    @69
    @50
    @75
    wceq
    @78
    @79
    @50
    @72
    @41
    cun
    #
    cF
    cfv
    #
    @75
    @69
    @77
    @50
    @93
    wceq
    @70
    @69
    @49
    @92
    cF
    @38
    cB
    ackbij1lem2
    #
    fveq2d
    3ad2ant3
    @77
    @70
    @93
    @75
    wceq
    #
    @69
    @77
    @84
    @41
    @1
    wcel
    #
    @72
    @41
    cin
    #
    c0
    wceq
    @95
    @87
    @77
    @3
    @41
    cB
    wss
    @96
    @66
    @2
    @3
    simprr
    cB
    @38
    inss1
    vx
    vy
    cB
    @41
    cF
    ackbij.f
    ackbij1lem11
    sylancl
    #
    @77
    @97
    @41
    @72
    cin
    #
    c0
    @72
    @41
    incom
    @77
    @41
    @38
    wss
    @90
    @99
    c0
    wceq
    cB
    @38
    inss2
    @91
    @41
    @38
    @72
    ssdisj
    sylancr
    syl5eq
    vx
    vy
    @72
    @41
    cF
    ackbij.f
    ackbij1lem9
    syl3anc
    3ad2ant1
    eqtrd
    syl3an1
    3eqtr3d
    @68
    @70
    @76
    @43
    wb
    #
    @69
    @66
    @4
    @100
    @51
    @77
    @73
    com
    wcel
    #
    @40
    com
    wcel
    #
    @42
    com
    wcel
    #
    @100
    @77
    @84
    @101
    @87
    @1
    com
    @72
    cF
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    #
    ffvelrni
    syl
    @77
    @85
    @102
    @88
    @1
    com
    @39
    cF
    @104
    ffvelrni
    syl
    @77
    @96
    @103
    @98
    @1
    com
    @41
    cF
    @104
    ffvelrni
    syl
    @73
    @40
    @42
    nnacan
    syl3anc
    3adant3
    3ad2ant1
    mpbid
    @70
    @69
    @44
    @52
    wi
    #
    @68
    @70
    @69
    wa
    #
    @44
    @52
    @106
    @44
    wa
    @80
    @92
    @47
    @49
    @44
    @80
    @92
    wceq
    @106
    @39
    @41
    @72
    uneq2
    adantl
    @70
    @47
    @80
    wceq
    @69
    @44
    @82
    ad2antrr
    @69
    @49
    @92
    wceq
    @70
    @44
    @94
    ad2antlr
    3eqtr4d
    ex
    3adant1
    embantd
    3exp
    @68
    @70
    wn
    #
    @69
    @67
    @68
    @107
    @69
    w3a
    #
    @50
    @48
    wceq
    #
    @67
    @108
    @48
    @50
    @66
    @4
    @51
    @107
    @69
    simp13
    eqcomd
    @108
    @3
    @2
    @66
    @69
    @107
    @109
    wn
    @2
    @3
    @66
    @51
    @107
    @69
    simp12r
    @2
    @3
    @66
    @51
    @107
    @69
    simp12l
    @66
    @4
    @51
    @107
    @69
    simp11
    @68
    @107
    @69
    simp3
    @68
    @107
    @69
    simp2
    vx
    vy
    cB
    cA
    cF
    vb
    ackbij.f
    ackbij1lem15
    syl23anc
    pm2.21dd
    3exp
    pm2.61d
    @68
    @70
    @69
    wn
    #
    @67
    wi
    @68
    @70
    @110
    @67
    @68
    @70
    @110
    w3a
    #
    @51
    @67
    @66
    @4
    @51
    @70
    @110
    simp13
    @111
    @2
    @3
    @66
    @70
    @110
    @51
    wn
    @2
    @3
    @66
    @51
    @70
    @110
    simp12l
    @2
    @3
    @66
    @51
    @70
    @110
    simp12r
    @66
    @4
    @51
    @70
    @110
    simp11
    @68
    @70
    @110
    simp2
    @68
    @70
    @110
    simp3
    vx
    vy
    cA
    cB
    cF
    vb
    ackbij.f
    ackbij1lem15
    syl23anc
    pm2.21dd
    3exp
    @68
    @107
    @110
    @67
    @68
    @107
    @110
    w3a
    #
    @43
    @44
    @52
    @112
    @51
    @43
    @66
    @4
    @51
    @107
    @110
    simp13
    @107
    @110
    @51
    @43
    wi
    @68
    @107
    @110
    wa
    #
    @51
    @43
    @113
    @48
    @40
    @50
    @42
    @113
    @47
    @39
    cF
    @107
    @47
    @39
    wceq
    @110
    @38
    cA
    ackbij1lem1
    adantr
    #
    fveq2d
    @113
    @49
    @41
    cF
    @110
    @49
    @41
    wceq
    @107
    @38
    cB
    ackbij1lem1
    adantl
    #
    fveq2d
    eqeq12d
    biimpd
    3adant1
    mpd
    @107
    @110
    @105
    @68
    @113
    @52
    @44
    @113
    @47
    @39
    @49
    @41
    @114
    @115
    eqeq12d
    biimprd
    3adant1
    embantd
    3exp
    pm2.61d
    pm2.61d
    3exp
    com34
    a2d
    finds
    mpcom
    @4
    @9
    @14
    @11
    @15
    @4
    @8
    cA
    cF
    @4
    cA
    @7
    wss
    @8
    cA
    wceq
    @4
    cA
    cB
    @7
    @4
    @5
    con0
    wss
    @5
    @7
    wss
    @4
    @5
    com
    con0
    @21
    omsson
    syl6ss
    @5
    onsucuni
    syl
    #
    unssad
    cA
    @7
    df-ss
    sylib
    #
    fveq2d
    @4
    @10
    cB
    cF
    @4
    cB
    @7
    wss
    @10
    cB
    wceq
    @4
    cA
    cB
    @7
    @116
    unssbd
    cB
    @7
    df-ss
    sylib
    #
    fveq2d
    eqeq12d
    @4
    @8
    cA
    @10
    cB
    @117
    @118
    eqeq12d
    3imtr3d
end
