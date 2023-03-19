include "caa.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0p.mm"
include "wne.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "ccoe.mm"
include "cabs.mm"
include "cn0.mm"
include "wral.mm"
include "w3a.mm"
include "cz.mm"
include "cply.mm"
include "crab.mm"
include "wrex.mm"
include "cc.mm"
include "cab.mm"
include "cuni.mm"
include "crn.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "cpr.mm"
include "cfz.mm"
include "co.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "simp3.mm"
include "eldifi.mm"
include "adantr.mm"
include "3adant2.mm"
include "eldifsni.mm"
include "wss.mm"
include "0nn0.mm"
include "dgrcl.mm"
include "syl.mm"
include "prssi.mm"
include "sylancr.mm"
include "ssrab2.mm"
include "a1i.mm"
include "unssd.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "syl6ss.mm"
include "fvex.mm"
include "prid2.mm"
include "elun1.mm"
include "ax-mp.mm"
include "supxrub.mm"
include "sylancl.mm"
include "fveq2.mm"
include "abs0.mm"
include "syl6eq.mm"
include "c0ex.mm"
include "prid1.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "wf.mm"
include "0z.mm"
include "eqid.mm"
include "coef2.mm"
include "ffvelrnda.mm"
include "nn0abscl.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "dgrub.mm"
include "syl3anc.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "weq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elun2.mm"
include "pm2.61dane.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "neeq1.mm"
include "breq1d.mm"
include "fveq1d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "simp2.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "cfn.mm"
include "c0.mm"
include "prfi.mm"
include "fzfi.mm"
include "abrexfi.mm"
include "rabssab.mm"
include "ssfi.mm"
include "mp2an.mm"
include "unfi.mm"
include "ne0ii.mm"
include "wor.mm"
include "xrltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "sseldd.mm"
include "eqidd.mm"
include "breq2.mm"
include "3anbi23d.mm"
include "rabbidv.mm"
include "rexeqdv.mm"
include "cnex.mm"
include "rabex.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "3exp.mm"
include "rexlimiv.mm"
include "impcom.mm"
include "simp1.mm"
include "anim2i.mm"
include "eldifsn.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "ssrexv.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "rexlimivw.mm"
include "exlimiv.mm"
include "impbii.mm"
include "elaa.mm"
include "eluniab.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "eqtr4i.mm"

theorem aannenlem2
  let ve: setvar e
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  assume aannenlem.a: |- H = ( a e. NN0 |-> { b e. CC | E. c e. { d e. ( Poly ` ZZ ) | ( d =/= 0p /\ ( deg ` d ) <_ a /\ A. e e. NN0 ( abs ` ( ( coeff ` d ) ` e ) ) <_ a ) } ( c ` b ) = 0 } )

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A i
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b i
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint g h
  disjoint g i
  disjoint h i
  assert |- AA = U. ran H

  proof
    caa
    vf
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vc
    vd
    cv
    #
    c0p
    wne
    #
    @5
    cdgr
    cfv
    #
    va
    cv
    #
    cle
    wbr
    #
    ve
    cv
    #
    @5
    ccoe
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    @8
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    vd
    cz
    cply
    cfv
    #
    crab
    #
    wrex
    #
    vb
    cc
    crab
    #
    wceq
    #
    va
    cn0
    wrex
    #
    vf
    cab
    #
    cuni
    #
    cH
    crn
    #
    cuni
    vg
    caa
    @24
    vg
    cv
    #
    cc
    wcel
    #
    @26
    vh
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vh
    @17
    c0p
    csn
    #
    cdif
    #
    wrex
    #
    wa
    #
    @26
    @0
    wcel
    #
    @22
    wa
    #
    vf
    wex
    #
    @26
    caa
    wcel
    @26
    @24
    wcel
    @34
    @37
    @33
    @27
    @37
    @30
    @27
    @37
    wi
    vh
    @32
    @28
    @32
    wcel
    #
    @30
    @27
    @37
    @38
    @30
    @27
    w3a
    #
    @26
    @4
    vc
    @6
    @7
    cc0
    @28
    cdgr
    cfv
    #
    cpr
    #
    @26
    vi
    cv
    #
    @28
    ccoe
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    wceq
    #
    vi
    cc0
    @40
    cfz
    co
    #
    wrex
    #
    vg
    cn0
    crab
    #
    cun
    #
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    @13
    @51
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    vd
    @17
    crab
    #
    wrex
    #
    vb
    cc
    crab
    #
    wcel
    #
    @58
    @20
    wceq
    #
    va
    cn0
    wrex
    #
    @37
    @39
    @27
    @26
    @2
    cfv
    #
    cc0
    wceq
    #
    vc
    @56
    wrex
    #
    @59
    @38
    @30
    @27
    simp3
    @39
    @28
    @56
    wcel
    #
    @30
    @64
    @39
    @28
    @17
    wcel
    #
    @28
    c0p
    wne
    #
    @40
    @51
    cle
    wbr
    #
    @10
    @43
    cfv
    #
    cabs
    cfv
    #
    @51
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    @65
    @38
    @27
    @66
    @30
    @38
    @66
    @27
    @28
    @17
    @31
    eldifi
    adantr
    #
    3adant2
    @38
    @27
    @73
    @30
    @38
    @27
    wa
    #
    @67
    @68
    @72
    @38
    @67
    @27
    @28
    @17
    c0p
    eldifsni
    adantr
    @75
    @50
    cxr
    wss
    #
    @40
    @50
    wcel
    #
    @68
    @75
    @50
    cn0
    cxr
    @75
    @41
    @49
    cn0
    @75
    cc0
    cn0
    wcel
    @40
    cn0
    wcel
    #
    @41
    cn0
    wss
    0nn0
    @75
    @66
    @78
    @74
    cz
    @28
    dgrcl
    syl
    #
    cc0
    @40
    cn0
    prssi
    sylancr
    @49
    cn0
    wss
    @75
    @48
    vg
    cn0
    ssrab2
    a1i
    unssd
    #
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    syl6ss
    #
    @40
    @41
    wcel
    @77
    cc0
    @40
    @28
    cdgr
    fvex
    prid2
    @40
    @41
    @49
    elun1
    ax-mp
    #
    @50
    @40
    supxrub
    sylancl
    @75
    @71
    ve
    cn0
    @75
    @10
    cn0
    wcel
    #
    wa
    #
    @76
    @70
    @50
    wcel
    #
    @71
    @75
    @76
    @83
    @81
    adantr
    @84
    @85
    @69
    cc0
    @69
    cc0
    wceq
    #
    @85
    @84
    @86
    @70
    cc0
    @50
    @86
    @70
    cc0
    cabs
    cfv
    cc0
    @69
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    cc0
    @41
    wcel
    cc0
    @50
    wcel
    cc0
    @40
    c0ex
    prid1
    cc0
    @41
    @49
    elun1
    ax-mp
    syl6eqel
    adantl
    @84
    @69
    cc0
    wne
    #
    wa
    #
    @70
    @49
    wcel
    #
    @85
    @88
    @70
    cn0
    wcel
    #
    @70
    @45
    wceq
    #
    vi
    @47
    wrex
    #
    @89
    @84
    @90
    @87
    @84
    @69
    cz
    wcel
    @90
    @75
    cn0
    cz
    @10
    @43
    @75
    @66
    cc0
    cz
    wcel
    cn0
    cz
    @43
    wf
    @74
    0z
    @43
    cz
    @28
    @43
    eqid
    #
    coef2
    sylancl
    ffvelrnda
    @69
    nn0abscl
    syl
    adantr
    @88
    @10
    @47
    wcel
    #
    @70
    @70
    wceq
    #
    @92
    @88
    @83
    @78
    @10
    @40
    cle
    wbr
    #
    @94
    @75
    @83
    @87
    simplr
    #
    @75
    @78
    @83
    @87
    @79
    ad2antrr
    @88
    @66
    @83
    @87
    @96
    @75
    @66
    @83
    @87
    @74
    ad2antrr
    @97
    @84
    @87
    simpr
    @43
    cz
    @28
    @10
    @40
    @93
    @40
    eqid
    dgrub
    syl3anc
    @10
    @40
    elfz2nn0
    syl3anbrc
    @70
    eqid
    @91
    @95
    vi
    @10
    @47
    vi
    ve
    weq
    #
    @45
    @70
    @70
    @98
    @44
    @69
    cabs
    @42
    @10
    @43
    fveq2
    fveq2d
    eqeq2d
    rspcev
    sylancl
    @48
    @92
    vg
    @70
    cn0
    @26
    @70
    wceq
    @46
    @91
    vi
    @47
    @26
    @70
    @45
    eqeq1
    rexbidv
    elrab
    sylanbrc
    @70
    @49
    @41
    elun2
    syl
    pm2.61dane
    @50
    @70
    supxrub
    syl2anc
    ralrimiva
    3jca
    3adant2
    @55
    @73
    vd
    @28
    @17
    vd
    vh
    weq
    #
    @6
    @67
    @52
    @68
    @54
    @72
    @5
    @28
    c0p
    neeq1
    #
    @99
    @7
    @40
    @51
    cle
    @5
    @28
    cdgr
    fveq2
    #
    breq1d
    @99
    @53
    @71
    ve
    cn0
    @99
    @13
    @70
    @51
    cle
    @99
    @12
    @69
    cabs
    @99
    @10
    @11
    @43
    @5
    @28
    ccoe
    fveq2
    fveq1d
    fveq2d
    #
    breq1d
    ralbidv
    3anbi123d
    elrab
    sylanbrc
    @38
    @30
    @27
    simp2
    @63
    @30
    vc
    @28
    @56
    vc
    vh
    weq
    @62
    @29
    cc0
    @26
    @2
    @28
    fveq1
    eqeq1d
    #
    rspcev
    syl2anc
    @57
    @64
    vb
    @26
    cc
    vb
    vg
    weq
    #
    @4
    @63
    vc
    @56
    @104
    @3
    @62
    cc0
    @1
    @26
    @2
    fveq2
    eqeq1d
    #
    rexbidv
    elrab
    sylanbrc
    @39
    @51
    cn0
    wcel
    #
    @58
    @58
    wceq
    #
    @61
    @38
    @27
    @106
    @30
    @75
    @50
    cn0
    @51
    @80
    @75
    @50
    cfn
    wcel
    #
    @50
    c0
    wne
    #
    @76
    @51
    @50
    wcel
    #
    @108
    @75
    @41
    cfn
    wcel
    @49
    cfn
    wcel
    #
    @108
    cc0
    @40
    prfi
    @48
    vg
    cab
    #
    cfn
    wcel
    #
    @49
    @112
    wss
    @111
    @47
    cfn
    wcel
    @113
    cc0
    @40
    fzfi
    vi
    vg
    @47
    @45
    abrexfi
    ax-mp
    @48
    vg
    cn0
    rabssab
    @112
    @49
    ssfi
    mp2an
    @41
    @49
    unfi
    mp2an
    a1i
    @109
    @75
    @40
    @50
    @82
    ne0ii
    a1i
    @81
    cxr
    clt
    wor
    @108
    @109
    @76
    w3a
    @110
    xrltso
    cxr
    @50
    clt
    fisupcl
    mpan
    syl3anc
    sseldd
    3adant2
    @39
    @58
    eqidd
    @60
    @107
    va
    @51
    cn0
    @8
    @51
    wceq
    #
    @20
    @58
    @58
    @114
    @19
    @57
    vb
    cc
    @114
    @4
    vc
    @18
    @56
    @114
    @16
    @55
    vd
    @17
    @114
    @9
    @52
    @15
    @54
    @6
    @8
    @51
    @7
    cle
    breq2
    @114
    @14
    @53
    ve
    cn0
    @8
    @51
    @13
    cle
    breq2
    ralbidv
    3anbi23d
    rabbidv
    rexeqdv
    rabbidv
    eqeq2d
    rspcev
    syl2anc
    @36
    @59
    @61
    wa
    vf
    @58
    @57
    vb
    cc
    cnex
    rabex
    @0
    @58
    wceq
    #
    @35
    @59
    @22
    @61
    @0
    @58
    @26
    eleq2
    @115
    @21
    @60
    va
    cn0
    @0
    @58
    @20
    eqeq1
    rexbidv
    anbi12d
    spcev
    syl2anc
    3exp
    rexlimiv
    impcom
    @36
    @34
    vf
    @22
    @35
    @34
    @21
    @35
    @34
    wi
    va
    cn0
    @21
    @35
    @26
    @20
    wcel
    #
    @34
    @0
    @20
    @26
    eleq2
    @116
    @27
    @63
    vc
    @18
    wrex
    #
    wa
    @34
    @19
    @117
    vb
    @26
    cc
    @104
    @4
    @63
    vc
    @18
    @105
    rexbidv
    elrab
    @117
    @33
    @27
    @18
    @32
    wss
    #
    @117
    @33
    wi
    vh
    @18
    @32
    @66
    @67
    @40
    @8
    cle
    wbr
    #
    @70
    @8
    cle
    wbr
    #
    ve
    cn0
    wral
    #
    w3a
    #
    wa
    @66
    @67
    wa
    @28
    @18
    wcel
    @38
    @122
    @67
    @66
    @67
    @119
    @121
    simp1
    anim2i
    @16
    @122
    vd
    @28
    @17
    @99
    @6
    @67
    @9
    @119
    @15
    @121
    @100
    @99
    @7
    @40
    @8
    cle
    @101
    breq1d
    @99
    @14
    @120
    ve
    cn0
    @99
    @13
    @70
    @8
    cle
    @102
    breq1d
    ralbidv
    3anbi123d
    elrab
    @28
    @17
    c0p
    eldifsn
    3imtr4i
    ssriv
    @118
    @117
    @63
    vc
    @32
    wrex
    @33
    @63
    vc
    @18
    @32
    ssrexv
    @63
    @30
    vc
    vh
    @32
    @103
    cbvrexv
    syl6ib
    ax-mp
    anim2i
    sylbi
    syl6bi
    rexlimivw
    impcom
    exlimiv
    impbii
    @26
    vh
    elaa
    @22
    vf
    @26
    eluniab
    3bitr4i
    eqriv
    @25
    @23
    va
    vf
    cn0
    @20
    cH
    aannenlem.a
    rnmpt
    unieqi
    eqtr4i
end
