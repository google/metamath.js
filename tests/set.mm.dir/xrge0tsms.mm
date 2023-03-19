include "ctsu.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cv.mm"
include "wss.mm"
include "cres.mm"
include "cgsu.mm"
include "wi.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "cxr.mm"
include "wbr.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wf.mm"
include "wa.mm"
include "iccssxr.mm"
include "cbs.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cmnf.mm"
include "cdif.mm"
include "cress.mm"
include "csubmnd.mm"
include "c0g.mm"
include "eqid.mm"
include "xrge0subm.mm"
include "cvv.mm"
include "xrex.mm"
include "difexg.mm"
include "wne.mm"
include "simpl.mm"
include "ge0nemnf.mm"
include "jca.mm"
include "elxrge0.mm"
include "eldifsn.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "xrs10.mm"
include "subm0.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "eqeltri.mm"
include "a1i.mm"
include "elfpw.mm"
include "simprbi.mm"
include "adantl.mm"
include "simplbi.mm"
include "fssres.mm"
include "syl2an.mm"
include "c0ex.mm"
include "fdmfifsupp.mm"
include "gsumcl.mm"
include "sseldi.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "supxrcl.mm"
include "syl5eqel.mm"
include "c0.mm"
include "cc.mm"
include "0ss.mm"
include "0fin.mm"
include "mpbir2an.mm"
include "0cn.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "gsum0.mm"
include "elrnmpt1s.mm"
include "supxrub.mm"
include "sylancl.mm"
include "syl6breqr.mm"
include "sylanbrc.mm"
include "ctop.mm"
include "wb.mm"
include "letop.mm"
include "ovex.mm"
include "elrest.mm"
include "inss1.mm"
include "sseli.mm"
include "cr.mm"
include "cioo.mm"
include "ctg.mm"
include "simplrl.mm"
include "reex.mm"
include "elrestr.mm"
include "mp3an12.mm"
include "xrtgioo.mm"
include "syl6eleqr.mm"
include "simplrr.mm"
include "simpr.mm"
include "elind.mm"
include "tg2.mm"
include "syl2anc.mm"
include "cxp.mm"
include "wfn.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "simprrr.mm"
include "adantr.mm"
include "syl6ss.mm"
include "simprrl.mm"
include "simp-4l.mm"
include "fssresd.mm"
include "simprll.mm"
include "ssfi.mm"
include "sstrd.mm"
include "simprlr.mm"
include "xrge0gsumle.mm"
include "xrltletrd.mm"
include "weq.mm"
include "eliooord.mm"
include "simprd.mm"
include "xrlelttrd.mm"
include "w3a.mm"
include "elioo1.mm"
include "mpbir3and.mm"
include "sseldd.mm"
include "anassrs.mm"
include "expr.mm"
include "ralrimiva.mm"
include "simpld.mm"
include "syl6breq.mm"
include "ad3antrrr.mm"
include "supxrlub.mm"
include "mpbid.mm"
include "rgenw.mm"
include "cbvmptv.mm"
include "breq2.mm"
include "rexrnmpt.mm"
include "sylib.mm"
include "reximddv.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "cioc.mm"
include "eqeltrrd.mm"
include "pnfnei.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "ad2antrl.mm"
include "simp-5l.mm"
include "rexr.mm"
include "simprl.mm"
include "pnfge.mm"
include "pnfxr.mm"
include "elioc1.mm"
include "ltpnf.mm"
include "simplr.mm"
include "breqtrrd.mm"
include "rexlimddv.mm"
include "wo.mm"
include "xrnemnf.mm"
include "mpjaodan.mm"
include "syl5.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "imbi12d.mm"
include "rexlimdva.mm"
include "ralrimiv.mm"
include "cts.mm"
include "xrstset.mm"
include "resstset.mm"
include "topnval.mm"
include "ctps.mm"
include "xrstps.mm"
include "resstps.mm"
include "eltsms.mm"
include "mpbir2and.mm"
include "cha.mm"
include "ctsr.mm"
include "letsr.mm"
include "ordthaus.mm"
include "mp1i.mm"
include "resthaus.mm"
include "haustsms2.mm"

theorem xrge0tsms
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume xrge0tsms.g: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume xrge0tsms.a: |- ( ph -> A e. V )
  assume xrge0tsms.f: |- ( ph -> F : A --> ( 0 [,] +oo ) )
  assume xrge0tsms.s: |- S = sup ( ran ( s e. ( ~P A i^i Fin ) |-> ( G gsum ( F |` s ) ) ) , RR* , < )

  disjoint A s
  disjoint F s
  disjoint ph s
  disjoint G s
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s y
  disjoint s z
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F r
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint ph r
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint G r
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint S r
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint S z
  assert |- ( ph -> ( G tsums F ) = { S } )

  proof
    wph
    cS
    cG
    cF
    ctsu
    co
    #
    wcel
    #
    @0
    cS
    csn
    wceq
    wph
    @1
    cS
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cS
    vu
    cv
    #
    wcel
    #
    vz
    cv
    #
    vy
    cv
    #
    wss
    #
    cG
    cF
    @7
    cres
    #
    cgsu
    co
    #
    @4
    wcel
    #
    wi
    #
    vy
    cA
    cpw
    cfn
    cin
    #
    wral
    vz
    @13
    wrex
    #
    wi
    #
    vu
    cle
    cordt
    cfv
    #
    @2
    crest
    co
    #
    wral
    wph
    cS
    cxr
    wcel
    #
    cc0
    cS
    cle
    wbr
    #
    @3
    wph
    cS
    vs
    @13
    cG
    cF
    vs
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cxr
    xrge0tsms.s
    wph
    @24
    cxr
    wss
    #
    @25
    cxr
    wcel
    wph
    @13
    cxr
    @23
    wf
    @26
    wph
    vs
    @13
    @22
    cxr
    @23
    wph
    @20
    @13
    wcel
    #
    wa
    #
    @2
    cxr
    @22
    cc0
    cpnf
    iccssxr
    #
    @28
    @20
    @2
    @21
    cG
    cfn
    cc0
    @2
    cxr
    wss
    @2
    cG
    cbs
    cfv
    wceq
    @29
    @2
    cxr
    cG
    cxrs
    xrge0tsms.g
    xrsbas
    ressbas2
    ax-mp
    #
    @2
    cxrs
    cxr
    cmnf
    csn
    #
    cdif
    #
    cress
    co
    #
    csubmnd
    cfv
    wcel
    cc0
    cG
    c0g
    cfv
    wceq
    @33
    @33
    eqid
    #
    xrge0subm
    @2
    cG
    @33
    cc0
    cG
    cxrs
    @2
    cress
    co
    #
    @33
    @2
    cress
    co
    #
    xrge0tsms.g
    @32
    cvv
    wcel
    #
    @2
    @32
    wss
    @36
    @35
    wceq
    cxr
    cvv
    wcel
    @37
    xrex
    cxr
    @31
    cvv
    difexg
    ax-mp
    vx
    @2
    @32
    vx
    cv
    #
    cxr
    wcel
    #
    cc0
    @38
    cle
    wbr
    #
    wa
    #
    @39
    @38
    cmnf
    wne
    #
    wa
    @38
    @2
    wcel
    @38
    @32
    wcel
    @41
    @39
    @42
    @39
    @40
    simpl
    @38
    ge0nemnf
    jca
    @38
    elxrge0
    @38
    cxr
    cmnf
    eldifsn
    3imtr4i
    ssriv
    @32
    @2
    cxrs
    cvv
    ressabs
    mp2an
    eqtr4i
    @33
    @34
    xrs10
    subm0
    ax-mp
    #
    cG
    ccmn
    wcel
    #
    @28
    cG
    @35
    ccmn
    xrge0tsms.g
    xrge0cmn
    eqeltri
    #
    a1i
    @27
    @20
    cfn
    wcel
    #
    wph
    @27
    @20
    cA
    wss
    #
    @46
    @20
    cA
    elfpw
    #
    simprbi
    adantl
    #
    wph
    cA
    @2
    cF
    wf
    #
    @47
    @20
    @2
    @21
    wf
    @27
    xrge0tsms.f
    @27
    @47
    @46
    @48
    simplbi
    cA
    @2
    @20
    cF
    fssres
    syl2an
    #
    @28
    @20
    @2
    @21
    cvv
    cc0
    @51
    @49
    cc0
    cvv
    wcel
    #
    @28
    c0ex
    a1i
    fdmfifsupp
    gsumcl
    sseldi
    @23
    eqid
    #
    fmptd
    @13
    cxr
    @23
    frn
    syl
    #
    @24
    supxrcl
    syl
    syl5eqel
    #
    wph
    cc0
    @25
    cS
    cle
    wph
    @26
    cc0
    @24
    wcel
    #
    cc0
    @25
    cle
    wbr
    @54
    c0
    @13
    wcel
    #
    cc0
    cc
    wcel
    @56
    @57
    c0
    cA
    wss
    c0
    cfn
    wcel
    cA
    0ss
    0fin
    c0
    cA
    elfpw
    mpbir2an
    0cn
    vs
    @13
    @22
    cc0
    c0
    @23
    cc
    @53
    @20
    c0
    wceq
    #
    @22
    cG
    c0
    cgsu
    co
    cc0
    @58
    @21
    c0
    cG
    cgsu
    @58
    @21
    cF
    c0
    cres
    c0
    @20
    c0
    cF
    reseq2
    cF
    res0
    syl6eq
    oveq2d
    cG
    cc0
    @43
    gsum0
    syl6eq
    elrnmpt1s
    mp2an
    @24
    cc0
    supxrub
    sylancl
    xrge0tsms.s
    syl6breqr
    #
    cS
    elxrge0
    sylanbrc
    wph
    @15
    vu
    @17
    @4
    @17
    wcel
    #
    @4
    vv
    cv
    #
    @2
    cin
    #
    wceq
    #
    vv
    @16
    wrex
    #
    wph
    @15
    @16
    ctop
    wcel
    #
    @2
    cvv
    wcel
    #
    @60
    @64
    wb
    letop
    cc0
    cpnf
    cicc
    ovex
    #
    vv
    @4
    @2
    @16
    ctop
    cvv
    elrest
    mp2an
    wph
    @63
    @15
    vv
    @16
    wph
    @61
    @16
    wcel
    #
    wa
    #
    @15
    @63
    cS
    @62
    wcel
    #
    @8
    @10
    @62
    wcel
    #
    wi
    #
    vy
    @13
    wral
    #
    vz
    @13
    wrex
    #
    wi
    @70
    cS
    @61
    wcel
    #
    @69
    @74
    @62
    @61
    cS
    @61
    @2
    inss1
    sseli
    wph
    @68
    @75
    @74
    wph
    @68
    @75
    wa
    #
    wa
    #
    cS
    cr
    wcel
    #
    @74
    cS
    cpnf
    wceq
    #
    @77
    @78
    wa
    #
    @5
    @4
    @61
    cr
    cin
    #
    wss
    #
    wa
    #
    vu
    cioo
    crn
    #
    wrex
    #
    @74
    @80
    @81
    @84
    ctg
    cfv
    #
    wcel
    cS
    @81
    wcel
    @85
    @80
    @81
    @16
    cr
    crest
    co
    #
    @86
    @80
    @68
    @81
    @87
    wcel
    #
    wph
    @68
    @75
    @78
    simplrl
    @65
    cr
    cvv
    wcel
    @68
    @88
    letop
    reex
    @61
    cr
    @16
    ctop
    cvv
    elrestr
    mp3an12
    syl
    @87
    @87
    eqid
    xrtgioo
    syl6eleqr
    @80
    @61
    cr
    cS
    wph
    @68
    @75
    @78
    simplrr
    @77
    @78
    simpr
    elind
    vu
    @81
    @84
    cS
    tg2
    syl2anc
    @80
    @83
    @74
    vu
    @84
    @4
    @84
    wcel
    #
    @4
    vr
    cv
    #
    vw
    cv
    #
    cioo
    co
    #
    wceq
    #
    vw
    cxr
    wrex
    vr
    cxr
    wrex
    #
    @80
    @83
    @74
    wi
    #
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @96
    wfn
    @89
    @94
    wb
    ioof
    @96
    @97
    cioo
    ffn
    vr
    vw
    cxr
    cxr
    @4
    cioo
    ovelrn
    mp2b
    @80
    @93
    @95
    vr
    vw
    cxr
    cxr
    @80
    @90
    cxr
    wcel
    #
    @91
    cxr
    wcel
    #
    wa
    #
    wa
    @95
    @93
    cS
    @92
    wcel
    #
    @92
    @81
    wss
    #
    wa
    #
    @74
    wi
    @80
    @100
    @103
    @74
    @80
    @100
    @103
    wa
    #
    wa
    #
    @90
    cG
    cF
    @6
    cres
    #
    cgsu
    co
    #
    clt
    wbr
    #
    @73
    vz
    @13
    @105
    @6
    @13
    wcel
    #
    @108
    wa
    #
    wa
    #
    @72
    vy
    @13
    @111
    @7
    @13
    wcel
    #
    @8
    @71
    @105
    @110
    @112
    @8
    wa
    #
    @71
    @105
    @110
    @113
    wa
    #
    wa
    #
    @61
    @2
    @10
    @115
    @92
    @61
    @10
    @115
    @92
    @81
    @61
    @105
    @102
    @114
    @80
    @100
    @101
    @102
    simprrr
    adantr
    @61
    cr
    inss1
    syl6ss
    @115
    @10
    @92
    wcel
    #
    @10
    cxr
    wcel
    #
    @90
    @10
    clt
    wbr
    #
    @10
    @91
    clt
    wbr
    #
    @115
    @2
    cxr
    @10
    @29
    @115
    @7
    @2
    @9
    cG
    cfn
    cc0
    @30
    @43
    @44
    @115
    @45
    a1i
    #
    @115
    @112
    @7
    cfn
    wcel
    #
    @105
    @110
    @112
    @8
    simprrl
    #
    @112
    @7
    cA
    wss
    #
    @121
    @7
    cA
    elfpw
    #
    simprbi
    #
    syl
    #
    @115
    cA
    @2
    @7
    cF
    @115
    wph
    @50
    wph
    @76
    @78
    @104
    @114
    simp-4l
    #
    xrge0tsms.f
    syl
    #
    @115
    @112
    @123
    @122
    @112
    @123
    @121
    @124
    simplbi
    #
    syl
    #
    fssresd
    #
    @115
    @7
    @2
    @9
    cvv
    cc0
    @131
    @126
    @52
    @115
    c0ex
    a1i
    #
    fdmfifsupp
    gsumcl
    #
    sseldi
    #
    @115
    @90
    @107
    @10
    @105
    @98
    @114
    @80
    @98
    @99
    @103
    simprll
    #
    adantr
    #
    @115
    @2
    cxr
    @107
    @29
    @115
    @6
    @2
    @106
    cG
    cfn
    cc0
    @30
    @43
    @120
    @115
    @121
    @8
    @6
    cfn
    wcel
    #
    @126
    @105
    @110
    @112
    @8
    simprrr
    #
    @7
    @6
    ssfi
    #
    syl2anc
    #
    @115
    cA
    @2
    @6
    cF
    @128
    @115
    @6
    @7
    cA
    @138
    @130
    sstrd
    fssresd
    #
    @115
    @6
    @2
    @106
    cvv
    cc0
    @141
    @140
    @132
    fdmfifsupp
    gsumcl
    sseldi
    @134
    @105
    @109
    @108
    @113
    simprlr
    @115
    cA
    @7
    @6
    cF
    cG
    cV
    xrge0tsms.g
    @115
    wph
    cA
    cV
    wcel
    #
    @127
    xrge0tsms.a
    syl
    @128
    @122
    @138
    xrge0gsumle
    xrltletrd
    @115
    @10
    cS
    @91
    @134
    @115
    wph
    @18
    @127
    @55
    syl
    @105
    @99
    @114
    @80
    @98
    @99
    @103
    simprlr
    adantr
    #
    @115
    @10
    @25
    cS
    cle
    @115
    @26
    @10
    @24
    wcel
    #
    @10
    @25
    cle
    wbr
    @115
    wph
    @26
    @127
    @54
    syl
    @115
    @112
    @10
    cvv
    wcel
    @144
    @122
    cG
    @9
    cgsu
    ovex
    vs
    @13
    @22
    @10
    @7
    @23
    cvv
    @53
    vs
    vy
    weq
    @21
    @9
    cG
    cgsu
    @20
    @7
    cF
    reseq2
    oveq2d
    elrnmpt1s
    sylancl
    @24
    @10
    supxrub
    syl2anc
    xrge0tsms.s
    syl6breqr
    @105
    cS
    @91
    clt
    wbr
    #
    @114
    @105
    @90
    cS
    clt
    wbr
    #
    @145
    @105
    @101
    @146
    @145
    wa
    @80
    @100
    @101
    @102
    simprrl
    cS
    @90
    @91
    eliooord
    syl
    #
    simprd
    adantr
    xrlelttrd
    @115
    @98
    @99
    @116
    @117
    @118
    @119
    w3a
    wb
    @136
    @143
    @90
    @91
    @10
    elioo1
    syl2anc
    mpbir3and
    sseldd
    @133
    elind
    anassrs
    expr
    ralrimiva
    @105
    @90
    @91
    clt
    wbr
    #
    vw
    @24
    wrex
    #
    @108
    vz
    @13
    wrex
    #
    @105
    @90
    @25
    clt
    wbr
    #
    @149
    @105
    @90
    cS
    @25
    clt
    @105
    @146
    @145
    @147
    simpld
    xrge0tsms.s
    syl6breq
    @105
    @26
    @98
    @151
    @149
    wb
    #
    wph
    @26
    @76
    @78
    @104
    @54
    ad3antrrr
    @135
    vw
    @24
    @90
    supxrlub
    #
    syl2anc
    mpbid
    @107
    cvv
    wcel
    #
    vz
    @13
    wral
    @149
    @150
    wb
    @154
    vz
    @13
    cG
    @106
    cgsu
    ovex
    rgenw
    @148
    @108
    vz
    vw
    @13
    @107
    @23
    cvv
    vs
    vz
    @13
    @22
    @107
    vs
    vz
    weq
    @21
    @106
    cG
    cgsu
    @20
    @6
    cF
    reseq2
    oveq2d
    cbvmptv
    @91
    @107
    @90
    clt
    breq2
    rexrnmpt
    ax-mp
    #
    sylib
    reximddv
    expr
    @93
    @83
    @103
    @74
    @93
    @5
    @101
    @82
    @102
    @4
    @92
    cS
    eleq2
    @4
    @92
    @81
    sseq1
    anbi12d
    imbi1d
    syl5ibrcom
    rexlimdvva
    syl5bi
    rexlimdv
    mpd
    @77
    @79
    wa
    #
    @90
    cpnf
    cioc
    co
    #
    @61
    wss
    #
    @74
    vr
    cr
    @156
    @68
    cpnf
    @61
    wcel
    @158
    vr
    cr
    wrex
    wph
    @68
    @75
    @79
    simplrl
    @156
    cS
    cpnf
    @61
    @77
    @79
    simpr
    wph
    @68
    @75
    @79
    simplrr
    eqeltrrd
    vr
    @61
    pnfnei
    syl2anc
    @156
    @90
    cr
    wcel
    #
    @158
    wa
    #
    wa
    #
    @108
    @73
    vz
    @13
    @161
    @110
    wa
    #
    @72
    vy
    @13
    @162
    @112
    @8
    @71
    @162
    @113
    wa
    #
    @61
    @2
    @10
    @163
    @157
    @61
    @10
    @161
    @158
    @110
    @113
    @156
    @159
    @158
    simprr
    ad2antrr
    @163
    @10
    @157
    wcel
    #
    @117
    @118
    @10
    cpnf
    cle
    wbr
    #
    @163
    @2
    cxr
    @10
    @29
    @163
    @7
    @2
    @9
    cG
    cfn
    cc0
    @30
    @43
    @44
    @163
    @45
    a1i
    #
    @112
    @121
    @162
    @8
    @125
    ad2antrl
    #
    @163
    cA
    @2
    @7
    cF
    @163
    wph
    @50
    wph
    @76
    @79
    @160
    @110
    @113
    simp-5l
    #
    xrge0tsms.f
    syl
    #
    @112
    @123
    @162
    @8
    @129
    ad2antrl
    #
    fssresd
    #
    @163
    @7
    @2
    @9
    cvv
    cc0
    @171
    @167
    @52
    @163
    c0ex
    a1i
    #
    fdmfifsupp
    gsumcl
    #
    sseldi
    #
    @163
    @90
    @107
    @10
    @161
    @98
    @110
    @113
    @159
    @98
    @156
    @158
    @90
    rexr
    ad2antrl
    #
    ad2antrr
    #
    @163
    @2
    cxr
    @107
    @29
    @163
    @6
    @2
    @106
    cG
    cfn
    cc0
    @30
    @43
    @166
    @163
    @121
    @8
    @137
    @167
    @162
    @112
    @8
    simprr
    #
    @139
    syl2anc
    #
    @163
    cA
    @2
    @6
    cF
    @169
    @163
    @6
    @7
    cA
    @177
    @170
    sstrd
    fssresd
    #
    @163
    @6
    @2
    @106
    cvv
    cc0
    @179
    @178
    @172
    fdmfifsupp
    gsumcl
    sseldi
    @174
    @161
    @109
    @108
    @113
    simplrr
    @163
    cA
    @7
    @6
    cF
    cG
    cV
    xrge0tsms.g
    @163
    wph
    @142
    @168
    xrge0tsms.a
    syl
    @169
    @162
    @112
    @8
    simprl
    @177
    xrge0gsumle
    xrltletrd
    @163
    @117
    @165
    @174
    @10
    pnfge
    syl
    @163
    @98
    cpnf
    cxr
    wcel
    @164
    @117
    @118
    @165
    w3a
    wb
    @176
    pnfxr
    @90
    cpnf
    @10
    elioc1
    sylancl
    mpbir3and
    sseldd
    @173
    elind
    expr
    ralrimiva
    @161
    @149
    @150
    @161
    @151
    @149
    @161
    @90
    cS
    @25
    clt
    @161
    @90
    cpnf
    cS
    clt
    @159
    @90
    cpnf
    clt
    wbr
    @156
    @158
    @90
    ltpnf
    ad2antrl
    @77
    @79
    @160
    simplr
    breqtrrd
    xrge0tsms.s
    syl6breq
    @161
    @26
    @98
    @152
    wph
    @26
    @76
    @79
    @160
    @54
    ad3antrrr
    @175
    @153
    syl2anc
    mpbid
    @155
    sylib
    reximddv
    rexlimddv
    @77
    @18
    cS
    cmnf
    wne
    #
    wa
    #
    @78
    @79
    wo
    wph
    @181
    @76
    wph
    @18
    @180
    @55
    wph
    @18
    @19
    @180
    @55
    @59
    cS
    ge0nemnf
    syl2anc
    jca
    adantr
    cS
    xrnemnf
    sylib
    mpjaodan
    expr
    syl5
    @63
    @5
    @70
    @14
    @74
    @4
    @62
    cS
    eleq2
    @63
    @12
    @72
    vz
    vy
    @13
    @13
    @63
    @11
    @71
    @8
    @4
    @62
    @10
    eleq2
    imbi2d
    rexralbidv
    imbi12d
    syl5ibrcom
    rexlimdva
    syl5bi
    ralrimiv
    wph
    vy
    vz
    vu
    cA
    @2
    cS
    @13
    cF
    cG
    @17
    cV
    @30
    @2
    @16
    cG
    @30
    @66
    @16
    cG
    cts
    cfv
    wceq
    @67
    @2
    cxrs
    cG
    @16
    cvv
    xrge0tsms.g
    xrstset
    resstset
    ax-mp
    topnval
    #
    @13
    eqid
    @44
    wph
    @45
    a1i
    #
    cG
    ctps
    wcel
    wph
    cG
    @35
    ctps
    xrge0tsms.g
    cxrs
    ctps
    wcel
    @66
    @35
    ctps
    wcel
    xrstps
    @67
    @2
    cxrs
    cvv
    resstps
    mp2an
    eqeltri
    a1i
    #
    xrge0tsms.a
    xrge0tsms.f
    eltsms
    mpbir2and
    wph
    cA
    @2
    cF
    cG
    @17
    cV
    cS
    @30
    @183
    @184
    xrge0tsms.a
    xrge0tsms.f
    @182
    wph
    @16
    cha
    wcel
    #
    @66
    @17
    cha
    wcel
    cle
    ctsr
    wcel
    @185
    wph
    letsr
    cle
    ordthaus
    mp1i
    @67
    @2
    @16
    cvv
    resthaus
    sylancl
    haustsms2
    mpd
end
