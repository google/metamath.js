include "wpo.mm"
include "cid.mm"
include "cres.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "ccom.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "po0.mm"
include "res0.mm"
include "ineq2i.mm"
include "in0.mm"
include "eqtri.mm"
include "xp0.mm"
include "coeq2i.mm"
include "co02.mm"
include "0ss.mm"
include "eqsstri.mm"
include "pm3.2i.mm"
include "2th.mm"
include "poeq2.mm"
include "reseq2.mm"
include "ineq2d.mm"
include "eqeq1d.mm"
include "xpeq2.mm"
include "coeq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "mpbiri.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "r19.28zv.mm"
include "ralbidv.mm"
include "bitrd.mm"
include "r19.26.mm"
include "syl6bb.mm"
include "df-po.mm"
include "wcel.mm"
include "wal.mm"
include "disj.mm"
include "df-ral.mm"
include "cop.mm"
include "opex.mm"
include "eleq1.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "cvv.mm"
include "vex.mm"
include "ididg.mm"
include "ax-mp.mm"
include "brres.mm"
include "mpbiran.mm"
include "bitr3i.mm"
include "notbid.mm"
include "imbi12d.mm"
include "spcv.mm"
include "con2d.mm"
include "alrimiv.mm"
include "wex.mm"
include "wrel.mm"
include "relres.mm"
include "elrel.mm"
include "mpan.mm"
include "ancri.mm"
include "weq.mm"
include "breq12.mm"
include "anidms.mm"
include "spv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "biimpcd.mm"
include "impd.mm"
include "syl.mm"
include "ideq.mm"
include "anbi1i.mm"
include "3bitr3ri.mm"
include "syl5ibrcom.mm"
include "exlimdvv.mm"
include "syl5.mm"
include "impbii.mm"
include "bitr4i.mm"
include "3bitri.mm"
include "wrex.mm"
include "ralcom.mm"
include "r19.23v.mm"
include "ralbii.mm"
include "bitri.mm"
include "brin.mm"
include "anbi12i.mm"
include "an4.mm"
include "ancom.mm"
include "brxp.mm"
include "anandi.mm"
include "3bitr4i.mm"
include "anass.mm"
include "exbii.mm"
include "brco.mm"
include "df-rex.mm"
include "r19.42v.mm"
include "imbi12i.mm"
include "2albii.mm"
include "r2al.mm"
include "impexp.mm"
include "relco.mm"
include "ssrel.mm"
include "bitr2i.mm"
include "3bitr4g.mm"
include "pm2.61ine.mm"

theorem dfpo2
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( R Po A <-> ( ( R i^i ( _I |` A ) ) = (/) /\ ( ( R i^i ( A X. A ) ) o. ( R i^i ( A X. A ) ) ) C_ R ) )

  proof
    cA
    cR
    wpo
    #
    cR
    cid
    cA
    cres
    #
    cin
    #
    c0
    wceq
    #
    cR
    cA
    cA
    cxp
    #
    cin
    #
    @5
    ccom
    #
    cR
    wss
    #
    wa
    #
    wb
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @9
    c0
    cR
    wpo
    #
    cR
    cid
    c0
    cres
    #
    cin
    #
    c0
    wceq
    #
    @5
    cR
    cA
    c0
    cxp
    #
    cin
    #
    ccom
    #
    cR
    wss
    #
    wa
    #
    wb
    @11
    @19
    cR
    po0
    @14
    @18
    @13
    cR
    c0
    cin
    #
    c0
    @12
    c0
    cR
    cid
    res0
    ineq2i
    cR
    in0
    #
    eqtri
    @17
    c0
    cR
    @17
    @5
    c0
    ccom
    c0
    @16
    c0
    @5
    @16
    @20
    c0
    @15
    c0
    cR
    cA
    xp0
    ineq2i
    @21
    eqtri
    coeq2i
    @5
    co02
    eqtri
    cR
    0ss
    eqsstri
    pm3.2i
    2th
    @10
    @0
    @11
    @8
    @19
    cA
    c0
    cR
    poeq2
    @10
    @3
    @14
    @7
    @18
    @10
    @2
    @13
    c0
    @10
    @1
    @12
    cR
    cA
    c0
    cid
    reseq2
    ineq2d
    eqeq1d
    @10
    @6
    @17
    cR
    @10
    @5
    @16
    @5
    @10
    @4
    @15
    cR
    cA
    c0
    cA
    xpeq2
    ineq2d
    coeq2d
    sseq1d
    anbi12d
    bibi12d
    mpbiri
    cA
    c0
    wne
    #
    vx
    cv
    #
    @23
    cR
    wbr
    #
    wn
    #
    @23
    vy
    cv
    #
    cR
    wbr
    #
    @26
    vz
    cv
    #
    cR
    wbr
    #
    wa
    #
    @23
    @28
    cR
    wbr
    #
    wi
    #
    wa
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @25
    vx
    cA
    wral
    #
    @32
    vz
    cA
    wral
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wa
    #
    @0
    @8
    @22
    @35
    @25
    @38
    wa
    #
    vx
    cA
    wral
    @40
    @22
    @34
    @41
    vx
    cA
    @22
    @34
    @25
    @37
    wa
    #
    vy
    cA
    wral
    @41
    @22
    @33
    @42
    vy
    cA
    @25
    @32
    vz
    cA
    r19.28zv
    ralbidv
    @25
    @37
    vy
    cA
    r19.28zv
    bitrd
    ralbidv
    @25
    @38
    vx
    cA
    r19.26
    syl6bb
    vx
    vy
    vz
    cA
    cR
    df-po
    @3
    @36
    @7
    @39
    @3
    vw
    cv
    #
    @1
    wcel
    #
    wn
    #
    vw
    cR
    wral
    @43
    cR
    wcel
    #
    @45
    wi
    #
    vw
    wal
    #
    @36
    vw
    cR
    @1
    disj
    @45
    vw
    cR
    df-ral
    @48
    @23
    cA
    wcel
    #
    @25
    wi
    #
    vx
    wal
    #
    @36
    @48
    @51
    @48
    @50
    vx
    @48
    @24
    @49
    @47
    @24
    @49
    wn
    #
    wi
    vw
    @23
    @23
    cop
    #
    @23
    @23
    opex
    @43
    @53
    wceq
    #
    @46
    @24
    @45
    @52
    @54
    @46
    @53
    cR
    wcel
    @24
    @43
    @53
    cR
    eleq1
    @23
    @23
    cR
    df-br
    syl6bbr
    @54
    @44
    @49
    @54
    @44
    @53
    @1
    wcel
    #
    @49
    @43
    @53
    @1
    eleq1
    @49
    @23
    @23
    @1
    wbr
    #
    @55
    @56
    @23
    @23
    cid
    wbr
    #
    @49
    @23
    cvv
    wcel
    @57
    vx
    vex
    #
    @23
    cvv
    ididg
    ax-mp
    @23
    @23
    cid
    cA
    @58
    brres
    mpbiran
    @23
    @23
    @1
    df-br
    bitr3i
    syl6bbr
    notbid
    imbi12d
    spcv
    con2d
    alrimiv
    @51
    @47
    vw
    @51
    @44
    @46
    @44
    @43
    @26
    @28
    cop
    #
    wceq
    #
    vz
    wex
    vy
    wex
    #
    @44
    wa
    @51
    @46
    wn
    #
    @44
    @61
    @1
    wrel
    @44
    @61
    cid
    cA
    relres
    vy
    vz
    @43
    @1
    elrel
    mpan
    ancri
    @51
    @61
    @44
    @62
    @51
    @60
    @44
    @62
    wi
    #
    vy
    vz
    @51
    @63
    @60
    vy
    vz
    weq
    #
    @26
    cA
    wcel
    #
    wa
    #
    @29
    wn
    #
    wi
    #
    @51
    @65
    @26
    @26
    cR
    wbr
    #
    wn
    #
    wi
    #
    @68
    @50
    @71
    vx
    vy
    vx
    vy
    weq
    #
    @49
    @65
    @25
    @70
    @23
    @26
    cA
    eleq1
    @72
    @24
    @69
    @72
    @24
    @69
    wb
    @23
    @26
    @23
    @26
    cR
    breq12
    anidms
    notbid
    imbi12d
    spv
    @71
    @64
    @65
    @67
    @64
    @71
    @65
    @67
    wi
    @64
    @70
    @67
    @65
    @64
    @69
    @29
    @26
    @28
    @26
    cR
    breq2
    notbid
    imbi2d
    biimpcd
    impd
    syl
    @60
    @44
    @66
    @62
    @67
    @60
    @44
    @59
    @1
    wcel
    #
    @66
    @43
    @59
    @1
    eleq1
    @26
    @28
    @1
    wbr
    @26
    @28
    cid
    wbr
    #
    @65
    wa
    @73
    @66
    @26
    @28
    cid
    cA
    vz
    vex
    #
    brres
    @26
    @28
    @1
    df-br
    @74
    @64
    @65
    @26
    @28
    @75
    ideq
    anbi1i
    3bitr3ri
    syl6bbr
    @60
    @46
    @29
    @60
    @46
    @59
    cR
    wcel
    @29
    @43
    @59
    cR
    eleq1
    @26
    @28
    cR
    df-br
    syl6bbr
    notbid
    imbi12d
    syl5ibrcom
    exlimdvv
    impd
    syl5
    con2d
    alrimiv
    impbii
    @25
    vx
    cA
    df-ral
    bitr4i
    3bitri
    @39
    @30
    vy
    cA
    wrex
    #
    @31
    wi
    #
    vz
    cA
    wral
    #
    vx
    cA
    wral
    #
    @7
    @38
    @78
    vx
    cA
    @38
    @32
    vy
    cA
    wral
    #
    vz
    cA
    wral
    @78
    @32
    vy
    vz
    cA
    cA
    ralcom
    @80
    @77
    vz
    cA
    @30
    @31
    vy
    cA
    r19.23v
    ralbii
    bitri
    ralbii
    @49
    @28
    cA
    wcel
    #
    wa
    #
    @76
    wa
    #
    @31
    wi
    #
    vz
    wal
    vx
    wal
    #
    @23
    @28
    cop
    #
    @6
    wcel
    #
    @86
    cR
    wcel
    #
    wi
    #
    vz
    wal
    vx
    wal
    #
    @79
    @7
    @84
    @89
    vx
    vz
    @83
    @87
    @31
    @88
    @23
    @26
    @5
    wbr
    #
    @26
    @28
    @5
    wbr
    #
    wa
    #
    vy
    wex
    #
    @65
    @82
    @30
    wa
    #
    wa
    #
    vy
    wex
    #
    @87
    @83
    @93
    @96
    vy
    @93
    @27
    @23
    @26
    @4
    wbr
    #
    wa
    #
    @29
    @26
    @28
    @4
    wbr
    #
    wa
    #
    wa
    #
    @65
    @82
    wa
    #
    @30
    wa
    #
    @96
    @91
    @99
    @92
    @101
    @23
    @26
    cR
    @4
    brin
    @26
    @28
    cR
    @4
    brin
    anbi12i
    @102
    @30
    @98
    @100
    wa
    #
    wa
    @105
    @30
    wa
    @104
    @27
    @98
    @29
    @100
    an4
    @30
    @105
    ancom
    @105
    @103
    @30
    @49
    @65
    wa
    #
    @65
    @81
    wa
    #
    wa
    @65
    @49
    wa
    #
    @107
    wa
    @105
    @103
    @106
    @108
    @107
    @49
    @65
    ancom
    anbi1i
    @98
    @106
    @100
    @107
    @23
    @26
    cA
    cA
    brxp
    @26
    @28
    cA
    cA
    brxp
    anbi12i
    @65
    @49
    @81
    anandi
    3bitr4i
    anbi1i
    3bitri
    @65
    @82
    @30
    anass
    3bitri
    exbii
    @94
    @23
    @28
    @6
    wbr
    @87
    vy
    @23
    @28
    @5
    @5
    @58
    @75
    brco
    @23
    @28
    @6
    df-br
    bitr3i
    @97
    @95
    vy
    cA
    wrex
    @83
    @95
    vy
    cA
    df-rex
    @82
    @30
    vy
    cA
    r19.42v
    bitr3i
    3bitr3ri
    @23
    @28
    cR
    df-br
    imbi12i
    2albii
    @79
    @82
    @77
    wi
    #
    vz
    wal
    vx
    wal
    @85
    @77
    vx
    vz
    cA
    cA
    r2al
    @84
    @109
    vx
    vz
    @82
    @76
    @31
    impexp
    2albii
    bitr4i
    @6
    wrel
    @7
    @90
    wb
    @5
    @5
    relco
    vx
    vz
    @6
    cR
    ssrel
    ax-mp
    3bitr4i
    bitr2i
    anbi12i
    3bitr4g
    pm2.61ine
end
