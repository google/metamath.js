include "cdr.mm"
include "wcel.mm"
include "cfn.mm"
include "cfrlm.mm"
include "co.mm"
include "clinds.mm"
include "cfv.mm"
include "w3a.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "clspn.mm"
include "cbs.mm"
include "wceq.mm"
include "clbs.mm"
include "simpl3.mm"
include "wss.mm"
include "clmod.mm"
include "crg.mm"
include "drngring.mm"
include "eqid.mm"
include "frlmlmod.mm"
include "sylan.mm"
include "linds1.mm"
include "lspssv.mm"
include "syl2an.mm"
include "3impa.mm"
include "adantr.mm"
include "cv.mm"
include "wn.mm"
include "wi.mm"
include "csdm.mm"
include "cdom.mm"
include "bren2.mm"
include "simprbi.mm"
include "csn.mm"
include "cun.mm"
include "wpss.mm"
include "snfi.mm"
include "simp2.mm"
include "lindsdom.mm"
include "domfi.mm"
include "syl2anc.mm"
include "unfi.mm"
include "sylancr.mm"
include "vex.mm"
include "snss.mm"
include "lspssid.mm"
include "sseld.mm"
include "syl5bir.mm"
include "con3dimp.mm"
include "nsspssun.mm"
include "sylib.mm"
include "php3.mm"
include "adantrl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "cvsca.mm"
include "cdif.mm"
include "csca.mm"
include "c0g.mm"
include "wral.mm"
include "snssi.mm"
include "3ad2ant3.mm"
include "unss.mm"
include "biimpi.mm"
include "syl2anr.mm"
include "simpr.mm"
include "difsn.mm"
include "syl.mm"
include "fveq2d.mm"
include "neleqtrrd.mm"
include "adantlr.mm"
include "difsnid.mm"
include "eleq2d.mm"
include "notbid.mm"
include "biimparc.mm"
include "adantll.mm"
include "clvec.mm"
include "frlmsca.mm"
include "simpl.mm"
include "eqeltrrd.mm"
include "islvec.mm"
include "sylanbrc.mm"
include "3adant3.mm"
include "ad4antr.mm"
include "ssdifssd.mm"
include "simp-4r.mm"
include "wb.mm"
include "difundir.mm"
include "equncomi.mm"
include "elsni.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "con2d.mm"
include "imp.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "adantllr.mm"
include "biimpa.mm"
include "cnzr.mm"
include "drngnzr.mm"
include "jca.mm"
include "anim1i.mm"
include "lindsind2.mm"
include "3expa.mm"
include "ad5ant14.mm"
include "eldifd.mm"
include "clss.mm"
include "lspsolv.mm"
include "syl13anc.mm"
include "mtand.mm"
include "ralrimiva.mm"
include "ralunb.mm"
include "weq.mm"
include "id.mm"
include "sneq.mm"
include "difeq2d.mm"
include "uncom.mm"
include "difeq1i.mm"
include "difun2.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "eleq12d.mm"
include "ralsn.mm"
include "anbi1i.mm"
include "bitri.mm"
include "ex.mm"
include "wne.mm"
include "ad3antrrr.mm"
include "eldifsn.mm"
include "adantl.mm"
include "3ad2antl3.mm"
include "sselda.mm"
include "lspsnvs.mm"
include "syl3anc.mm"
include "sseq1d.mm"
include "df-3an.mm"
include "lspcl.mm"
include "anassrs.mm"
include "sylanb.mm"
include "ad2antrr.mm"
include "eldifi.mm"
include "lmodvscl.mm"
include "lspsnel5.mm"
include "3bitr4rd.mm"
include "biimpd.mm"
include "ralrimdva.mm"
include "ralimdva.mm"
include "syld.mm"
include "impr.mm"
include "cvv.mm"
include "ovex.mm"
include "islinds2.mm"
include "ax-mp.mm"
include "sdomdomtr.mm"
include "stoic1a.mm"
include "sylan2.mm"
include "iman.mm"
include "sylibr.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "islbs4.mm"

theorem lindsenlbs
  let cR: class R
  let cI: class I
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( R e. DivRing /\ I e. Fin /\ X e. ( LIndS ` ( R freeLMod I ) ) ) /\ X ~~ I ) -> X e. ( LBasis ` ( R freeLMod I ) ) )

  proof
    cR
    cdr
    wcel
    #
    cI
    cfn
    wcel
    #
    cX
    cR
    cI
    cfrlm
    co
    #
    clinds
    cfv
    #
    wcel
    #
    w3a
    #
    cX
    cI
    cen
    wbr
    #
    wa
    #
    @4
    cX
    @2
    clspn
    cfv
    #
    cfv
    #
    @2
    cbs
    cfv
    #
    wceq
    cX
    @2
    clbs
    cfv
    #
    wcel
    @0
    @1
    @4
    @6
    simpl3
    @7
    @9
    @10
    @5
    @9
    @10
    wss
    #
    @6
    @0
    @1
    @4
    @12
    @0
    @1
    wa
    #
    @2
    clmod
    wcel
    #
    cX
    @10
    wss
    #
    @12
    @4
    @0
    cR
    crg
    wcel
    @1
    @14
    cR
    drngring
    cR
    @2
    cI
    cfn
    @2
    eqid
    #
    frlmlmod
    sylan
    #
    @10
    @2
    cX
    @10
    eqid
    #
    linds1
    #
    cX
    @8
    @10
    @2
    @18
    @8
    eqid
    #
    lspssv
    syl2an
    3impa
    adantr
    @7
    vy
    @10
    @9
    @7
    vy
    cv
    #
    @10
    wcel
    #
    @21
    @9
    wcel
    #
    wn
    #
    wa
    #
    wn
    #
    @22
    @23
    wi
    @6
    @5
    cX
    cI
    csdm
    wbr
    #
    wn
    #
    @26
    @6
    cX
    cI
    cdom
    wbr
    #
    @28
    cX
    cI
    bren2
    simprbi
    @5
    @25
    @27
    @5
    @25
    wa
    #
    cX
    @21
    csn
    #
    cX
    cun
    #
    csdm
    wbr
    #
    @32
    cI
    cdom
    wbr
    #
    @27
    @5
    @24
    @33
    @22
    @5
    @24
    wa
    #
    @32
    cfn
    wcel
    #
    cX
    @32
    wpss
    #
    @33
    @5
    @36
    @24
    @5
    @31
    cfn
    wcel
    cX
    cfn
    wcel
    #
    @36
    @21
    snfi
    @5
    @1
    @29
    @38
    @0
    @1
    @4
    simp2
    cR
    cI
    cX
    lindsdom
    cI
    cX
    domfi
    syl2anc
    @31
    cX
    unfi
    sylancr
    adantr
    @35
    @31
    cX
    wss
    #
    wn
    @37
    @5
    @39
    @23
    @39
    @21
    cX
    wcel
    #
    @5
    @23
    @21
    cX
    vy
    vex
    #
    snss
    @5
    cX
    @9
    @21
    @0
    @1
    @4
    cX
    @9
    wss
    #
    @13
    @14
    @15
    @42
    @4
    @17
    @19
    cX
    @8
    @10
    @2
    @18
    @20
    lspssid
    syl2an
    3impa
    sseld
    #
    syl5bir
    con3dimp
    @31
    cX
    nsspssun
    sylib
    @32
    cX
    php3
    syl2anc
    adantrl
    @30
    @0
    @1
    @32
    @3
    wcel
    #
    @34
    @0
    @1
    @4
    @25
    simpl1
    @0
    @1
    @4
    @25
    simpl2
    @30
    @32
    @10
    wss
    #
    vx
    cv
    #
    vz
    cv
    #
    @2
    cvsca
    cfv
    #
    co
    #
    @32
    @47
    csn
    #
    cdif
    #
    @8
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @2
    csca
    cfv
    #
    cbs
    cfv
    #
    @55
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vz
    @32
    wral
    #
    @44
    @25
    @31
    @10
    wss
    #
    @15
    @45
    @5
    @22
    @62
    @24
    @21
    @10
    snssi
    #
    adantr
    @4
    @0
    @15
    @1
    @19
    3ad2ant3
    @62
    @15
    wa
    @45
    @31
    cX
    @10
    unss
    biimpi
    #
    syl2anr
    @5
    @22
    @24
    @61
    @5
    @22
    wa
    #
    @24
    @47
    @52
    wcel
    #
    wn
    #
    vz
    @32
    wral
    #
    @61
    @65
    @24
    @68
    @65
    @24
    wa
    #
    @21
    cX
    @31
    cdif
    #
    @8
    cfv
    #
    wcel
    #
    wn
    #
    @67
    vz
    cX
    wral
    #
    @68
    @5
    @24
    @73
    @22
    @35
    @71
    @9
    @21
    @5
    @24
    simpr
    @35
    @70
    cX
    @8
    @35
    @40
    wn
    #
    @70
    cX
    wceq
    @5
    @40
    @23
    @43
    con3dimp
    #
    @21
    cX
    difsn
    syl
    fveq2d
    neleqtrrd
    adantlr
    @69
    @67
    vz
    cX
    @69
    @47
    cX
    wcel
    #
    wa
    #
    @66
    @21
    cX
    @50
    cdif
    #
    @50
    cun
    #
    @8
    cfv
    #
    wcel
    #
    @24
    @77
    @82
    wn
    #
    @65
    @77
    @83
    @24
    @77
    @82
    @23
    @77
    @81
    @9
    @21
    @77
    @80
    cX
    @8
    cX
    @47
    difsnid
    fveq2d
    eleq2d
    notbid
    biimparc
    adantll
    @78
    @66
    wa
    #
    @2
    clvec
    wcel
    #
    @79
    @10
    wss
    #
    @22
    @47
    @79
    @31
    cun
    #
    @8
    cfv
    #
    @79
    @8
    cfv
    #
    cdif
    wcel
    @82
    @5
    @85
    @22
    @24
    @77
    @66
    @0
    @1
    @85
    @4
    @13
    @14
    @55
    cdr
    wcel
    @85
    @17
    @13
    cR
    @55
    cdr
    cR
    @2
    cI
    cdr
    cfn
    @16
    frlmsca
    #
    @0
    @1
    simpl
    eqeltrrd
    @55
    @2
    @55
    eqid
    #
    islvec
    sylanbrc
    3adant3
    #
    ad4antr
    @5
    @86
    @22
    @24
    @77
    @66
    @4
    @0
    @86
    @1
    @4
    cX
    @10
    @50
    @19
    ssdifssd
    3ad2ant3
    ad4antr
    @5
    @22
    @24
    @77
    @66
    simp-4r
    @84
    @47
    @88
    @89
    @78
    @66
    @47
    @88
    wcel
    #
    @5
    @24
    @77
    @66
    @93
    wb
    @22
    @35
    @77
    wa
    #
    @52
    @88
    @47
    @94
    @51
    @87
    @8
    @94
    @51
    @79
    @31
    @50
    cdif
    #
    cun
    @87
    @51
    @95
    @79
    @31
    cX
    @50
    difundir
    equncomi
    @94
    @95
    @31
    @79
    @94
    @47
    @31
    wcel
    #
    wn
    #
    @95
    @31
    wceq
    @35
    @77
    @97
    @35
    @96
    @77
    @35
    @77
    wn
    @96
    @75
    @76
    @96
    @77
    @40
    @96
    @47
    @21
    cX
    @47
    @21
    elsni
    eleq1d
    notbid
    syl5ibrcom
    con2d
    imp
    @47
    @31
    difsn
    syl
    uneq2d
    syl5eq
    fveq2d
    eleq2d
    adantllr
    biimpa
    @5
    @77
    @47
    @89
    wcel
    wn
    #
    @22
    @24
    @66
    @5
    @14
    @55
    cnzr
    wcel
    #
    wa
    #
    @4
    wa
    #
    @77
    @98
    @0
    @1
    @4
    @101
    @13
    @100
    @4
    @13
    @14
    @99
    @17
    @13
    cR
    @55
    cnzr
    @90
    @0
    cR
    cnzr
    wcel
    @1
    cR
    drngnzr
    adantr
    eqeltrrd
    jca
    anim1i
    3impa
    @100
    @4
    @77
    @98
    @47
    cX
    @8
    @55
    @2
    @20
    @91
    lindsind2
    3expa
    sylan
    ad5ant14
    eldifd
    @79
    @2
    clss
    cfv
    #
    @8
    @10
    @2
    @47
    @21
    @18
    @102
    eqid
    #
    @20
    lspsolv
    syl13anc
    mtand
    ralrimiva
    @68
    @67
    vz
    @31
    wral
    #
    @74
    wa
    @73
    @74
    wa
    @67
    vz
    @31
    cX
    ralunb
    @104
    @73
    @74
    @67
    @73
    vz
    @21
    @41
    vz
    vy
    weq
    #
    @66
    @72
    @105
    @47
    @21
    @52
    @71
    @105
    id
    @105
    @51
    @70
    @8
    @105
    @51
    @32
    @31
    cdif
    #
    @70
    @105
    @50
    @31
    @32
    @47
    @21
    sneq
    difeq2d
    @106
    cX
    @31
    cun
    #
    @31
    cdif
    @70
    @32
    @107
    @31
    @31
    cX
    uncom
    difeq1i
    cX
    @31
    difun2
    eqtri
    syl6eq
    fveq2d
    eleq12d
    notbid
    ralsn
    anbi1i
    bitri
    sylanbrc
    ex
    @65
    @67
    @60
    vz
    @32
    @65
    @47
    @32
    wcel
    #
    wa
    #
    @67
    @54
    vx
    @59
    @109
    @46
    @59
    wcel
    #
    wa
    #
    @67
    @54
    @111
    @66
    @53
    @111
    @49
    csn
    @8
    cfv
    #
    @52
    wss
    @50
    @8
    cfv
    #
    @52
    wss
    #
    @53
    @66
    @111
    @112
    @113
    @52
    @111
    @85
    @46
    @56
    wcel
    #
    @46
    @57
    wne
    wa
    #
    @47
    @10
    wcel
    #
    @112
    @113
    wceq
    @5
    @85
    @22
    @108
    @110
    @92
    ad3antrrr
    @110
    @116
    @109
    @110
    @116
    @46
    @56
    @57
    eldifsn
    biimpi
    adantl
    @109
    @117
    @110
    @65
    @32
    @10
    @47
    @4
    @0
    @22
    @45
    @1
    @22
    @62
    @15
    @45
    @4
    @63
    @19
    @64
    syl2anr
    #
    3ad2antl3
    sselda
    #
    adantr
    #
    @46
    @48
    @55
    @56
    @8
    @10
    @2
    @47
    @57
    @18
    @91
    @48
    eqid
    #
    @56
    eqid
    #
    @57
    eqid
    #
    @20
    lspsnvs
    syl3anc
    sseq1d
    @111
    @102
    @52
    @8
    @10
    @2
    @49
    @18
    @103
    @20
    @5
    @14
    @22
    @108
    @110
    @0
    @1
    @14
    @4
    @17
    3adant3
    #
    ad3antrrr
    #
    @65
    @52
    @102
    wcel
    #
    @108
    @110
    @5
    @13
    @4
    wa
    @22
    @126
    @0
    @1
    @4
    df-3an
    @13
    @4
    @22
    @126
    @13
    @14
    @51
    @10
    wss
    @126
    @4
    @22
    wa
    #
    @17
    @127
    @32
    @10
    @50
    @118
    ssdifssd
    @102
    @51
    @8
    @10
    @2
    @18
    @103
    @20
    lspcl
    syl2an
    anassrs
    sylanb
    #
    ad2antrr
    @111
    @14
    @115
    @117
    @49
    @10
    wcel
    @125
    @110
    @115
    @109
    @46
    @56
    @58
    eldifi
    adantl
    @120
    @46
    @48
    @55
    @56
    @10
    @2
    @47
    @18
    @91
    @121
    @122
    lmodvscl
    syl3anc
    lspsnel5
    @109
    @66
    @114
    wb
    @110
    @109
    @102
    @52
    @8
    @10
    @2
    @47
    @18
    @103
    @20
    @5
    @14
    @22
    @108
    @124
    ad2antrr
    @65
    @126
    @108
    @128
    adantr
    @119
    lspsnel5
    adantr
    3bitr4rd
    notbid
    biimpd
    ralrimdva
    ralimdva
    syld
    impr
    @2
    cvv
    wcel
    @44
    @45
    @61
    wa
    wb
    cR
    cI
    cfrlm
    ovex
    vz
    @10
    @55
    @48
    vx
    @32
    @8
    @56
    @2
    cvv
    @57
    @18
    @121
    @20
    @91
    @122
    @123
    islinds2
    ax-mp
    sylanbrc
    cR
    cI
    @32
    lindsdom
    syl3anc
    cX
    @32
    cI
    sdomdomtr
    syl2anc
    stoic1a
    sylan2
    @22
    @23
    iman
    sylibr
    ssrdv
    eqssd
    @10
    @11
    @8
    @2
    cX
    @18
    @11
    eqid
    @20
    islbs4
    sylanbrc
end
