include "crn.mm"
include "cuni.mm"
include "cnt.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "cbl.mm"
include "co.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "cxmt.mm"
include "wa.mm"
include "cms.mm"
include "cme.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "ctop.mm"
include "mopntop.mm"
include "syl.mm"
include "cpw.mm"
include "ccld.mm"
include "cn.mm"
include "wf.mm"
include "frn.mm"
include "eqid.mm"
include "cldss2.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "ntropn.mm"
include "syl2anc.mm"
include "jca.mm"
include "mopni2.mm"
include "3expa.mm"
include "sylan.mm"
include "wn.mm"
include "w3a.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "c1.mm"
include "cop.mm"
include "wceq.mm"
include "caddc.mm"
include "wral.mm"
include "cvv.mm"
include "csn.mm"
include "wex.mm"
include "mopnuni.mm"
include "topopn.mm"
include "eqeltrd.mm"
include "cr.mm"
include "reex.mm"
include "rpssre.mm"
include "ssexi.mm"
include "xpexg.mm"
include "sylancl.mm"
include "3ad2ant1.mm"
include "ntrss3.mm"
include "sseqtr4d.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "opelxpi.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "ccl.mm"
include "copab.mm"
include "opabssxp.mm"
include "wb.mm"
include "elpw2g.mm"
include "adantr.mm"
include "mpbiri.mm"
include "simpl.mm"
include "rspa.mm"
include "syl2an.mm"
include "ssdif0.mm"
include "c1st.mm"
include "c2nd.mm"
include "1st2nd2.mm"
include "ad2antll.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "bln0.mm"
include "syl3anc.mm"
include "eqnetrd.mm"
include "wi.mm"
include "ffvelrn.mm"
include "cldss.mm"
include "cxr.mm"
include "rpxrd.mm"
include "blopn.mm"
include "ssntr.mm"
include "expr.mm"
include "syl21anc.mm"
include "ssn0.mm"
include "expcom.mm"
include "sylsyld.mm"
include "syl5bir.mm"
include "necon2d.mm"
include "mpd.mm"
include "n0.mm"
include "difopn.mm"
include "3adant3.mm"
include "simp2l.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "mopni3.mm"
include "syl31anc.mm"
include "simp1.mm"
include "elssuni.mm"
include "ssdifssd.mm"
include "sseld.mm"
include "3impia.mm"
include "c2.mm"
include "rphalfcl.mm"
include "rphalflt.mm"
include "breq1.mm"
include "rspcev.mm"
include "ad2antlr.mm"
include "df-rex.mm"
include "simpr3.mm"
include "rpred.mm"
include "simpr1.mm"
include "simplrl.mm"
include "nnrecred.mm"
include "simpr2.mm"
include "lttr.mm"
include "expdimp.mm"
include "anim1i.mm"
include "rpxr.mm"
include "id.mm"
include "3anim123i.mm"
include "3coml.mm"
include "blsscls.mm"
include "sstr2.mm"
include "anim12d.mm"
include "simpllr.mm"
include "jctild.mm"
include "3exp2.mm"
include "com35.mm"
include "imp5d.mm"
include "eximdv.mm"
include "syl5bi.mm"
include "ex.mm"
include "rexlimdva.mm"
include "3expia.mm"
include "opabn0.mm"
include "sylibr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "1z.mm"
include "nnuz.mm"
include "axdc4uz.mm"
include "simpl1.mm"
include "simpl3.mm"
include "oveq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "bcthlem4.mm"
include "exlimddv.mm"
include "ntrss2.mm"
include "syl5com.mm"
include "syl6ib.mm"
include "necon3ad.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "eq0rdv.mm"

theorem bcthlem5
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let vr: setvar r
  let vg: setvar g
  let vn: setvar n
  let cA: class A
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vy: setvar y
  let cR: class R
  assume bcth.2: |- J = ( MetOpen ` D )
  assume bcthlem.4: |- ( ph -> D e. ( CMet ` X ) )
  assume bcthlem.5: |- F = ( k e. NN , z e. ( X X. RR+ ) |-> { <. x , r >. | ( ( x e. X /\ r e. RR+ ) /\ ( r < ( 1 / k ) /\ ( ( cls ` J ) ` ( x ( ball ` D ) r ) ) C_ ( ( ( ball ` D ) ` z ) \ ( M ` k ) ) ) ) } )
  assume bcthlem.6: |- ( ph -> M : NN --> ( Clsd ` J ) )
  assume bcthlem5.7: |- ( ph -> A. k e. NN ( ( int ` J ) ` ( M ` k ) ) = (/) )

  disjoint k r
  disjoint k x
  disjoint k z
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint D k
  disjoint D r
  disjoint D x
  disjoint D z
  disjoint F k
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J k
  disjoint J r
  disjoint J x
  disjoint J z
  disjoint M k
  disjoint M r
  disjoint M x
  disjoint M z
  disjoint k ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint X k
  disjoint X r
  disjoint X x
  disjoint X z
  disjoint g ph
  disjoint k n
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint A r
  disjoint A x
  disjoint A z
  disjoint B k
  disjoint B r
  disjoint B x
  disjoint B z
  disjoint C r
  disjoint C x
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g r
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n y
  disjoint D n
  disjoint r y
  disjoint x y
  disjoint y z
  disjoint D y
  disjoint F g
  disjoint F n
  disjoint J g
  disjoint J m
  disjoint J n
  disjoint J y
  disjoint M g
  disjoint M m
  disjoint M n
  disjoint M y
  disjoint m ph
  disjoint n ph
  disjoint R x
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X y
  assert |- ( ph -> ( ( int ` J ) ` U. ran M ) = (/) )

  proof
    wph
    vn
    cM
    crn
    #
    cuni
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    wph
    vn
    cv
    #
    @3
    wcel
    #
    @4
    vm
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @3
    wss
    #
    vm
    crp
    wrex
    #
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @3
    cJ
    wcel
    #
    wa
    @5
    @10
    wph
    @11
    @12
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    cD
    cX
    cme
    cfv
    wcel
    @11
    bcthlem.4
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    3syl
    #
    wph
    cJ
    ctop
    wcel
    #
    @1
    cJ
    cuni
    #
    wss
    #
    @12
    wph
    @11
    @15
    @14
    cD
    cJ
    cX
    bcth.2
    mopntop
    syl
    #
    wph
    @0
    @16
    cpw
    #
    wss
    @17
    wph
    @0
    cJ
    ccld
    cfv
    #
    @19
    wph
    cn
    @20
    cM
    wf
    #
    @0
    @20
    wss
    bcthlem.6
    cn
    @20
    cM
    frn
    syl
    cJ
    @16
    @16
    eqid
    #
    cldss2
    syl6ss
    @0
    @16
    sspwuni
    sylib
    #
    @1
    cJ
    @16
    @22
    ntropn
    syl2anc
    jca
    @11
    @12
    @5
    @10
    vm
    @3
    cD
    @4
    cJ
    cX
    bcth.2
    mopni2
    3expa
    sylan
    wph
    @5
    wa
    @9
    vm
    crp
    wph
    @5
    @6
    crp
    wcel
    #
    @9
    wn
    #
    wph
    @5
    @24
    w3a
    #
    @8
    @1
    cdif
    #
    c0
    wne
    #
    @25
    @26
    cn
    cX
    crp
    cxp
    #
    vg
    cv
    #
    wf
    #
    c1
    @30
    cfv
    @4
    @6
    cop
    #
    wceq
    #
    @4
    c1
    caddc
    co
    #
    @30
    cfv
    #
    @4
    @4
    @30
    cfv
    #
    cF
    co
    #
    wcel
    #
    vn
    cn
    wral
    #
    w3a
    #
    @28
    vg
    @26
    @29
    cvv
    wcel
    #
    @32
    @29
    wcel
    #
    cn
    @29
    cxp
    @29
    cpw
    #
    c0
    csn
    cdif
    #
    cF
    wf
    #
    @40
    vg
    wex
    wph
    @5
    @41
    @24
    wph
    cX
    cJ
    wcel
    crp
    cvv
    wcel
    @41
    wph
    cX
    @16
    cJ
    wph
    @11
    cX
    @16
    wceq
    #
    @14
    cD
    cJ
    cX
    bcth.2
    mopnuni
    syl
    #
    wph
    @15
    @16
    cJ
    wcel
    @18
    cJ
    @16
    @22
    topopn
    syl
    eqeltrd
    crp
    cr
    reex
    rpssre
    ssexi
    cX
    crp
    cJ
    cvv
    xpexg
    sylancl
    #
    3ad2ant1
    @26
    @4
    cX
    wcel
    #
    @24
    @42
    @26
    @3
    cX
    @4
    wph
    @5
    @3
    cX
    wss
    @24
    wph
    @3
    @16
    cX
    wph
    @15
    @17
    @3
    @16
    wss
    @18
    @23
    @1
    cJ
    @16
    @22
    ntrss3
    syl2anc
    @47
    sseqtr4d
    3ad2ant1
    wph
    @5
    @24
    simp2
    sseldd
    #
    wph
    @5
    @24
    simp3
    @4
    @6
    cX
    crp
    opelxpi
    syl2anc
    wph
    @5
    @45
    @24
    wph
    vx
    cv
    #
    cX
    wcel
    #
    vr
    cv
    #
    crp
    wcel
    #
    wa
    #
    @53
    c1
    vk
    cv
    #
    cdiv
    co
    #
    clt
    wbr
    #
    @51
    @53
    @7
    co
    cJ
    ccl
    cfv
    cfv
    #
    vz
    cv
    #
    @7
    cfv
    #
    @56
    cM
    cfv
    #
    cdif
    #
    wss
    #
    wa
    #
    wa
    #
    vx
    vr
    copab
    #
    @44
    wcel
    #
    vz
    @29
    wral
    vk
    cn
    wral
    @45
    wph
    @68
    vk
    vz
    cn
    @29
    wph
    @56
    cn
    wcel
    #
    @60
    @29
    wcel
    #
    wa
    #
    wa
    #
    @67
    @43
    wcel
    #
    @67
    c0
    wne
    #
    @68
    @72
    @73
    @67
    @29
    wss
    #
    @65
    vx
    vr
    cX
    crp
    opabssxp
    wph
    @73
    @75
    wb
    #
    @71
    wph
    @41
    @76
    @48
    @67
    @29
    cvv
    elpw2g
    syl
    adantr
    mpbiri
    @72
    @66
    vr
    wex
    #
    vx
    wex
    #
    @74
    @72
    @63
    c0
    wne
    #
    @78
    @72
    @62
    @2
    cfv
    #
    c0
    wceq
    #
    @79
    wph
    @81
    vk
    cn
    wral
    @69
    @81
    @71
    bcthlem5.7
    @69
    @70
    simpl
    #
    @81
    vk
    cn
    rspa
    syl2an
    @72
    @63
    c0
    @80
    c0
    @63
    c0
    wceq
    @61
    @62
    wss
    #
    @72
    @80
    c0
    wne
    #
    @61
    @62
    ssdif0
    @72
    @61
    c0
    wne
    #
    @83
    @61
    @80
    wss
    #
    @84
    @72
    @61
    @60
    c1st
    cfv
    #
    @60
    c2nd
    cfv
    #
    @7
    co
    #
    c0
    @72
    @61
    @87
    @88
    cop
    #
    @7
    cfv
    @89
    @72
    @60
    @90
    @7
    @70
    @60
    @90
    wceq
    wph
    @69
    @60
    cX
    crp
    1st2nd2
    ad2antll
    fveq2d
    @87
    @88
    @7
    df-ov
    syl6eqr
    #
    @72
    @11
    @87
    cX
    wcel
    #
    @88
    crp
    wcel
    #
    @89
    c0
    wne
    wph
    @11
    @71
    @14
    adantr
    #
    @70
    @92
    wph
    @69
    @60
    cX
    crp
    xp1st
    ad2antll
    #
    @70
    @93
    wph
    @69
    @60
    cX
    crp
    xp2nd
    ad2antll
    #
    cD
    @87
    @88
    cX
    bln0
    syl3anc
    eqnetrd
    @72
    @15
    @62
    @16
    wss
    #
    @61
    cJ
    wcel
    #
    @83
    @86
    wi
    wph
    @15
    @71
    @18
    adantr
    @72
    @62
    @20
    wcel
    #
    @97
    wph
    @21
    @69
    @99
    @71
    bcthlem.6
    @82
    cn
    @20
    @56
    cM
    ffvelrn
    syl2an
    #
    @62
    cJ
    @16
    @22
    cldss
    syl
    @72
    @61
    @89
    cJ
    @91
    @72
    @11
    @92
    @88
    cxr
    wcel
    @89
    cJ
    wcel
    @94
    @95
    @72
    @88
    @96
    rpxrd
    cD
    @87
    @88
    cJ
    cX
    bcth.2
    blopn
    syl3anc
    eqeltrd
    #
    @15
    @97
    wa
    @98
    @83
    @86
    @62
    cJ
    @61
    @16
    @22
    ssntr
    expr
    syl21anc
    @86
    @85
    @84
    @61
    @80
    ssn0
    expcom
    sylsyld
    syl5bir
    necon2d
    mpd
    @79
    @51
    @63
    wcel
    #
    vx
    wex
    @72
    @78
    vx
    @63
    n0
    @72
    @102
    @77
    vx
    wph
    @71
    @102
    @77
    wph
    @71
    @102
    w3a
    #
    @4
    @57
    clt
    wbr
    #
    @51
    @4
    @7
    co
    #
    @63
    wss
    #
    wa
    #
    vn
    crp
    wrex
    #
    @77
    @103
    @11
    @63
    cJ
    wcel
    #
    @102
    @57
    crp
    wcel
    #
    @108
    wph
    @71
    @11
    @102
    @14
    3ad2ant1
    wph
    @71
    @109
    @102
    @72
    @98
    @99
    @109
    @101
    @100
    @61
    @62
    cJ
    @16
    @22
    difopn
    syl2anc
    3adant3
    wph
    @71
    @102
    simp3
    @103
    @69
    @110
    wph
    @69
    @70
    @102
    simp2l
    @69
    @56
    @56
    nnrp
    rpreccld
    syl
    vn
    @63
    cD
    @51
    @57
    cJ
    cX
    bcth.2
    mopni3
    syl31anc
    @103
    wph
    @52
    @71
    @108
    @77
    wi
    wph
    @71
    @102
    simp1
    wph
    @71
    @102
    @52
    @72
    @63
    cX
    @51
    @72
    @61
    cX
    @62
    @72
    @61
    @16
    cX
    @72
    @98
    @61
    @16
    wss
    @101
    @61
    cJ
    elssuni
    syl
    wph
    @46
    @71
    @47
    adantr
    sseqtr4d
    ssdifssd
    sseld
    3impia
    wph
    @71
    @102
    simp2
    wph
    @52
    wa
    #
    @71
    wa
    #
    @107
    @77
    vn
    crp
    @112
    @4
    crp
    wcel
    #
    wa
    #
    @107
    @77
    @114
    @107
    wa
    #
    @53
    @4
    clt
    wbr
    #
    vr
    crp
    wrex
    #
    @77
    @113
    @117
    @112
    @107
    @113
    @4
    c2
    cdiv
    co
    #
    crp
    wcel
    @118
    @4
    clt
    wbr
    #
    @117
    @4
    rphalfcl
    @4
    rphalflt
    @116
    @119
    vr
    @118
    crp
    @53
    @118
    @4
    clt
    breq1
    rspcev
    syl2anc
    ad2antlr
    @117
    @54
    @116
    wa
    #
    vr
    wex
    @115
    @77
    @116
    vr
    crp
    df-rex
    @115
    @120
    @66
    vr
    @112
    @113
    @107
    @54
    @116
    @66
    @112
    @113
    @116
    @54
    @107
    @66
    @112
    @113
    @116
    @54
    @107
    @66
    wi
    @112
    @113
    @116
    @54
    w3a
    #
    wa
    #
    @107
    @65
    @55
    @122
    @104
    @58
    @106
    @64
    @122
    @53
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    @57
    cr
    wcel
    #
    @116
    @104
    @58
    wi
    @122
    @53
    @112
    @113
    @116
    @54
    simpr3
    #
    rpred
    @122
    @4
    @112
    @113
    @116
    @54
    simpr1
    rpred
    @122
    @56
    @111
    @69
    @70
    @121
    simplrl
    nnrecred
    @112
    @113
    @116
    @54
    simpr2
    @123
    @124
    @125
    w3a
    @116
    @104
    @58
    @53
    @4
    @57
    lttr
    expdimp
    syl31anc
    @122
    @59
    @105
    wss
    #
    @106
    @64
    wi
    @112
    @11
    @52
    wa
    #
    @53
    cxr
    wcel
    #
    @4
    cxr
    wcel
    #
    @116
    w3a
    #
    @127
    @121
    @111
    @128
    @71
    wph
    @11
    @52
    @14
    anim1i
    adantr
    @54
    @113
    @116
    @131
    @54
    @129
    @113
    @130
    @116
    @116
    @53
    rpxr
    @4
    rpxr
    @116
    id
    3anim123i
    3coml
    cD
    @51
    @53
    @4
    cJ
    cX
    bcth.2
    blsscls
    syl2an
    @59
    @105
    @63
    sstr2
    syl
    anim12d
    @122
    @52
    @54
    wph
    @52
    @71
    @121
    simpllr
    @126
    jca
    jctild
    3exp2
    com35
    imp5d
    eximdv
    syl5bi
    mpd
    ex
    rexlimdva
    syl21anc
    mpd
    3expia
    eximdv
    syl5bi
    mpd
    @66
    vx
    vr
    opabn0
    sylibr
    @67
    @43
    c0
    eldifsn
    sylanbrc
    ralrimivva
    vk
    vz
    cn
    @29
    @67
    @44
    cF
    bcthlem.5
    fmpt2
    sylib
    3ad2ant1
    @29
    @32
    vg
    vn
    cF
    c1
    cvv
    cn
    1z
    nnuz
    axdc4uz
    syl3anc
    @26
    @40
    wa
    #
    vx
    vz
    @4
    cD
    @6
    vg
    vk
    cF
    cJ
    cM
    cX
    vr
    bcth.2
    @132
    wph
    @13
    wph
    @5
    @24
    @40
    simpl1
    #
    bcthlem.4
    syl
    bcthlem.5
    @132
    wph
    @21
    @133
    bcthlem.6
    syl
    wph
    @5
    @24
    @40
    simpl3
    @26
    @49
    @40
    @50
    adantr
    @26
    @31
    @33
    @39
    simpr1
    @26
    @31
    @33
    @39
    simpr2
    @132
    @39
    @56
    c1
    caddc
    co
    #
    @30
    cfv
    #
    @56
    @56
    @30
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    cn
    wral
    @26
    @31
    @33
    @39
    simpr3
    @38
    @138
    vn
    vk
    cn
    @4
    @56
    wceq
    #
    @35
    @135
    @37
    @137
    @139
    @34
    @134
    @30
    @4
    @56
    c1
    caddc
    oveq1
    fveq2d
    @139
    @4
    @56
    @36
    @136
    cF
    @139
    id
    @4
    @56
    @30
    fveq2
    oveq12d
    eleq12d
    cbvralv
    sylib
    bcthlem4
    exlimddv
    wph
    @5
    @28
    @25
    wi
    @24
    wph
    @9
    @27
    c0
    wph
    @9
    @8
    @1
    wss
    #
    @27
    c0
    wceq
    wph
    @3
    @1
    wss
    #
    @9
    @140
    wph
    @15
    @17
    @141
    @18
    @23
    @1
    cJ
    @16
    @22
    ntrss2
    syl2anc
    @8
    @3
    @1
    sstr2
    syl5com
    @8
    @1
    ssdif0
    syl6ib
    necon3ad
    3ad2ant1
    mpd
    3expa
    nrexdv
    pm2.65da
    eq0rdv
end
