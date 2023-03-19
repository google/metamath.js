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
include "c0g.mm"
include "cbs.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "eqid.mm"
include "ccmn.mm"
include "cress.mm"
include "xrge0cmn.mm"
include "eqeltri.mm"
include "a1i.mm"
include "simpr.mm"
include "elfpw.mm"
include "simplbi.mm"
include "fssres.mm"
include "syl2an.mm"
include "cvv.mm"
include "elinel2.mm"
include "adantl.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "gsumcl.mm"
include "sseldi.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "supxrcl.mm"
include "eqeltrd.mm"
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
include "cmnf.mm"
include "cdif.mm"
include "csubmnd.mm"
include "xrge0subm.mm"
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
include "gsum0.mm"
include "elrnmpt1s.mm"
include "supxrub.mm"
include "sylancl.mm"
include "breqtrrd.mm"
include "sylanbrc.mm"
include "ctop.mm"
include "wb.mm"
include "letop.mm"
include "ovex.mm"
include "elrest.mm"
include "elinel1.mm"
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
include "inss1.mm"
include "syl6ss.mm"
include "simprrl.mm"
include "simp-4l.mm"
include "fssresd.mm"
include "wfun.mm"
include "ffun.mm"
include "ad2antrr.mm"
include "c0ex.mm"
include "resfifsupp.mm"
include "simprll.mm"
include "sstrd.mm"
include "ssfi.mm"
include "simprlr.mm"
include "xrge0gsumle.mm"
include "xrltletrd.mm"
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
include "ad3antrrr.mm"
include "breqtrd.mm"
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
include "simprl.mm"
include "simp-5l.mm"
include "ad2antrl.mm"
include "rexr.mm"
include "pnfge.mm"
include "pnfxr.mm"
include "elioc1.mm"
include "ltpnf.mm"
include "simplr.mm"
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

theorem xrge0tsmsd
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
  assume xrge0tsmsd.g: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume xrge0tsmsd.a: |- ( ph -> A e. V )
  assume xrge0tsmsd.f: |- ( ph -> F : A --> ( 0 [,] +oo ) )
  assume xrge0tsmsd.s: |- ( ph -> S = sup ( ran ( s e. ( ~P A i^i Fin ) |-> ( G gsum ( F |` s ) ) ) , RR* , < ) )

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
    #
    cfn
    cin
    #
    wral
    vz
    @14
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
    @14
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
    xrge0tsmsd.s
    wph
    @25
    cxr
    wss
    #
    @26
    cxr
    wcel
    wph
    @14
    cxr
    @24
    wf
    @27
    wph
    vs
    @14
    @23
    cxr
    @24
    wph
    @21
    @14
    wcel
    #
    wa
    #
    @2
    cxr
    @23
    cc0
    cpnf
    iccssxr
    #
    @29
    @21
    @2
    @22
    cG
    @14
    cG
    c0g
    cfv
    #
    @2
    cxr
    wss
    @2
    cG
    cbs
    cfv
    wceq
    @30
    @2
    cxr
    cG
    cxrs
    xrge0tsmsd.g
    xrsbas
    ressbas2
    ax-mp
    #
    @31
    eqid
    #
    cG
    ccmn
    wcel
    #
    @29
    cG
    cxrs
    @2
    cress
    co
    #
    ccmn
    xrge0tsmsd.g
    xrge0cmn
    eqeltri
    #
    a1i
    wph
    @28
    simpr
    wph
    cA
    @2
    cF
    wf
    #
    @21
    cA
    wss
    #
    @21
    @2
    @22
    wf
    @28
    xrge0tsmsd.f
    @28
    @38
    @21
    cfn
    wcel
    #
    @21
    cA
    elfpw
    simplbi
    cA
    @2
    @21
    cF
    fssres
    syl2an
    #
    @29
    @21
    @2
    @22
    cvv
    @31
    @40
    @28
    @39
    wph
    @21
    @13
    cfn
    elinel2
    adantl
    @29
    cG
    c0g
    fvexd
    fdmfifsupp
    gsumcl
    sseldi
    @24
    eqid
    #
    fmptd
    @14
    cxr
    @24
    frn
    syl
    #
    @25
    supxrcl
    syl
    eqeltrd
    #
    wph
    cc0
    @26
    cS
    cle
    wph
    @27
    cc0
    @25
    wcel
    #
    cc0
    @26
    cle
    wbr
    @42
    c0
    @14
    wcel
    #
    cc0
    cc
    wcel
    @44
    @45
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
    @14
    @23
    cc0
    c0
    @24
    cc
    @41
    @21
    c0
    wceq
    #
    @23
    cG
    c0
    cgsu
    co
    cc0
    @46
    @22
    c0
    cG
    cgsu
    @46
    @22
    cF
    c0
    cres
    c0
    @21
    c0
    cF
    reseq2
    cF
    res0
    syl6eq
    oveq2d
    cG
    cc0
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
    @31
    wceq
    @49
    @49
    eqid
    #
    xrge0subm
    @2
    cG
    @49
    cc0
    cG
    @35
    @49
    @2
    cress
    co
    #
    xrge0tsmsd.g
    @48
    cvv
    wcel
    #
    @2
    @48
    wss
    @51
    @35
    wceq
    cxr
    cvv
    wcel
    @52
    xrex
    cxr
    @47
    cvv
    difexg
    ax-mp
    vx
    @2
    @48
    vx
    cv
    #
    cxr
    wcel
    #
    cc0
    @53
    cle
    wbr
    #
    wa
    #
    @54
    @53
    cmnf
    wne
    #
    wa
    @53
    @2
    wcel
    @53
    @48
    wcel
    @56
    @54
    @57
    @54
    @55
    simpl
    @53
    ge0nemnf
    jca
    @53
    elxrge0
    @53
    cxr
    cmnf
    eldifsn
    3imtr4i
    ssriv
    @48
    @2
    cxrs
    cvv
    ressabs
    mp2an
    eqtr4i
    @49
    @50
    xrs10
    subm0
    ax-mp
    #
    gsum0
    syl6eq
    elrnmpt1s
    mp2an
    @25
    cc0
    supxrub
    sylancl
    xrge0tsmsd.s
    breqtrrd
    #
    cS
    elxrge0
    sylanbrc
    wph
    @16
    vu
    @18
    @4
    @18
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
    @17
    wrex
    #
    wph
    @16
    @17
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
    @17
    ctop
    cvv
    elrest
    mp2an
    wph
    @63
    @16
    vv
    @17
    wph
    @61
    @17
    wcel
    #
    wa
    #
    @16
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
    @14
    wral
    #
    vz
    @14
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
    cS
    @61
    @2
    elinel1
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
    @17
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
    @17
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
    @14
    @105
    @6
    @14
    wcel
    #
    @108
    wa
    #
    wa
    #
    @72
    vy
    @14
    @111
    @7
    @14
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
    @30
    @115
    @7
    @2
    @9
    cG
    cfn
    cc0
    @32
    @58
    @34
    @115
    @36
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
    @7
    @13
    cfn
    elinel2
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
    @37
    wph
    @76
    @78
    @104
    @114
    simp-4l
    #
    xrge0tsmsd.f
    syl
    #
    @115
    @112
    @7
    cA
    wss
    #
    @122
    @112
    @127
    @121
    @7
    cA
    elfpw
    simplbi
    #
    syl
    #
    fssresd
    @115
    cF
    cvv
    @7
    cc0
    @80
    cF
    wfun
    #
    @104
    @114
    wph
    @130
    @76
    @78
    wph
    @37
    @130
    xrge0tsmsd.f
    cA
    @2
    cF
    ffun
    syl
    ad2antrr
    ad2antrr
    @124
    cc0
    cvv
    wcel
    @115
    c0ex
    a1i
    resfifsupp
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
    @30
    @115
    @6
    @2
    @106
    cG
    @14
    @31
    @32
    @33
    @120
    @105
    @109
    @108
    @113
    simprll
    @115
    cA
    @2
    @6
    cF
    @126
    @115
    @6
    @7
    cA
    @105
    @110
    @112
    @8
    simprrr
    #
    @129
    sstrd
    fssresd
    #
    @115
    @6
    @2
    @106
    cvv
    @31
    @136
    @115
    @121
    @8
    @6
    cfn
    wcel
    #
    @124
    @135
    @7
    @6
    ssfi
    #
    syl2anc
    @115
    cG
    c0g
    fvexd
    fdmfifsupp
    gsumcl
    sseldi
    @132
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
    xrge0tsmsd.g
    @115
    wph
    cA
    cV
    wcel
    #
    @125
    xrge0tsmsd.a
    syl
    @126
    @122
    @135
    xrge0gsumle
    xrltletrd
    @115
    @10
    cS
    @91
    @132
    @115
    wph
    @19
    @125
    @43
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
    @26
    cS
    cle
    @115
    @27
    @10
    @25
    wcel
    #
    @10
    @26
    cle
    wbr
    @115
    wph
    @27
    @125
    @42
    syl
    @115
    @112
    @10
    cvv
    wcel
    @141
    @122
    cG
    @9
    cgsu
    ovex
    vs
    @14
    @23
    @10
    @7
    @24
    cvv
    @41
    @21
    @7
    wceq
    @22
    @9
    cG
    cgsu
    @21
    @7
    cF
    reseq2
    oveq2d
    elrnmpt1s
    sylancl
    @25
    @10
    supxrub
    syl2anc
    @115
    wph
    cS
    @26
    wceq
    #
    @125
    xrge0tsmsd.s
    syl
    breqtrrd
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
    @143
    @105
    @101
    @144
    @143
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
    @134
    @140
    @90
    @91
    @10
    elioo1
    syl2anc
    mpbir3and
    sseldd
    @131
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
    @25
    wrex
    #
    @108
    vz
    @14
    wrex
    #
    @105
    @90
    @26
    clt
    wbr
    #
    @147
    @105
    @90
    cS
    @26
    clt
    @105
    @144
    @143
    @145
    simpld
    wph
    @142
    @76
    @78
    @104
    xrge0tsmsd.s
    ad3antrrr
    breqtrd
    @105
    @27
    @98
    @149
    @147
    wb
    #
    wph
    @27
    @76
    @78
    @104
    @42
    ad3antrrr
    @133
    vw
    @25
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
    @14
    wral
    @147
    @148
    wb
    @152
    vz
    @14
    cG
    @106
    cgsu
    ovex
    rgenw
    @146
    @108
    vz
    vw
    @14
    @107
    @24
    cvv
    vs
    vz
    @14
    @23
    @107
    @21
    @6
    wceq
    @22
    @106
    cG
    cgsu
    @21
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
    @154
    @68
    cpnf
    @61
    wcel
    @156
    vr
    cr
    wrex
    wph
    @68
    @75
    @79
    simplrl
    @154
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
    @154
    @90
    cr
    wcel
    #
    @156
    wa
    #
    wa
    #
    @108
    @73
    vz
    @14
    @159
    @110
    wa
    #
    @72
    vy
    @14
    @160
    @112
    @8
    @71
    @160
    @113
    wa
    #
    @61
    @2
    @10
    @161
    @155
    @61
    @10
    @159
    @156
    @110
    @113
    @154
    @157
    @156
    simprr
    ad2antrr
    @161
    @10
    @155
    wcel
    #
    @117
    @118
    @10
    cpnf
    cle
    wbr
    #
    @161
    @2
    cxr
    @10
    @30
    @161
    @7
    @2
    @9
    cG
    @14
    @31
    @32
    @33
    @34
    @161
    @36
    a1i
    #
    @160
    @112
    @8
    simprl
    #
    @161
    cA
    @2
    @7
    cF
    @161
    wph
    @37
    wph
    @76
    @79
    @158
    @110
    @113
    simp-5l
    #
    xrge0tsmsd.f
    syl
    #
    @112
    @127
    @160
    @8
    @128
    ad2antrl
    #
    fssresd
    #
    @161
    @7
    @2
    @9
    cvv
    @31
    @169
    @112
    @121
    @160
    @8
    @123
    ad2antrl
    #
    @161
    cG
    c0g
    fvexd
    #
    fdmfifsupp
    gsumcl
    #
    sseldi
    #
    @161
    @90
    @107
    @10
    @159
    @98
    @110
    @113
    @157
    @98
    @154
    @156
    @90
    rexr
    ad2antrl
    #
    ad2antrr
    #
    @161
    @2
    cxr
    @107
    @30
    @161
    @6
    @2
    @106
    cG
    @14
    @31
    @32
    @33
    @164
    @159
    @109
    @108
    @113
    simplrl
    @161
    cA
    @2
    @6
    cF
    @167
    @161
    @6
    @7
    cA
    @160
    @112
    @8
    simprr
    #
    @168
    sstrd
    fssresd
    #
    @161
    @6
    @2
    @106
    cvv
    @31
    @177
    @161
    @121
    @8
    @137
    @170
    @176
    @138
    syl2anc
    @171
    fdmfifsupp
    gsumcl
    sseldi
    @173
    @159
    @109
    @108
    @113
    simplrr
    @161
    cA
    @7
    @6
    cF
    cG
    cV
    xrge0tsmsd.g
    @161
    wph
    @139
    @166
    xrge0tsmsd.a
    syl
    @167
    @165
    @176
    xrge0gsumle
    xrltletrd
    @161
    @117
    @163
    @173
    @10
    pnfge
    syl
    @161
    @98
    cpnf
    cxr
    wcel
    @162
    @117
    @118
    @163
    w3a
    wb
    @175
    pnfxr
    @90
    cpnf
    @10
    elioc1
    sylancl
    mpbir3and
    sseldd
    @172
    elind
    expr
    ralrimiva
    @159
    @147
    @148
    @159
    @149
    @147
    @159
    @90
    cS
    @26
    clt
    @159
    @90
    cpnf
    cS
    clt
    @157
    @90
    cpnf
    clt
    wbr
    @154
    @156
    @90
    ltpnf
    ad2antrl
    @77
    @79
    @158
    simplr
    breqtrrd
    wph
    @142
    @76
    @79
    @158
    xrge0tsmsd.s
    ad3antrrr
    breqtrd
    @159
    @27
    @98
    @150
    wph
    @27
    @76
    @79
    @158
    @42
    ad3antrrr
    @174
    @151
    syl2anc
    mpbid
    @153
    sylib
    reximddv
    rexlimddv
    @77
    @19
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
    @179
    @76
    wph
    @19
    @178
    @43
    wph
    @19
    @20
    @178
    @43
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
    @15
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
    @14
    @14
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
    @14
    cF
    cG
    @18
    cV
    @32
    @2
    @17
    cG
    @32
    @66
    @17
    cG
    cts
    cfv
    wceq
    @67
    @2
    cxrs
    cG
    @17
    cvv
    xrge0tsmsd.g
    xrstset
    resstset
    ax-mp
    topnval
    #
    @14
    eqid
    @34
    wph
    @36
    a1i
    #
    cG
    ctps
    wcel
    wph
    cG
    @35
    ctps
    xrge0tsmsd.g
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
    xrge0tsmsd.a
    xrge0tsmsd.f
    eltsms
    mpbir2and
    wph
    cA
    @2
    cF
    cG
    @18
    cV
    cS
    @32
    @181
    @182
    xrge0tsmsd.a
    xrge0tsmsd.f
    @180
    wph
    @17
    cha
    wcel
    #
    @66
    @18
    cha
    wcel
    cle
    ctsr
    wcel
    @183
    wph
    letsr
    cle
    ordthaus
    mp1i
    @67
    @2
    @17
    cvv
    resthaus
    sylancl
    haustsms2
    mpd
end
