include "cc0.mm"
include "cvol.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "citg2.mm"
include "wn.mm"
include "cle.mm"
include "wa.mm"
include "cn.mm"
include "ccnv.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cpnf.mm"
include "cioo.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "covol.mm"
include "cxr.mm"
include "wcel.mm"
include "cdm.mm"
include "cicc.mm"
include "iccssxr.mm"
include "volf.mm"
include "ffvelrni.mm"
include "sseldi.mm"
include "syl.mm"
include "adantr.mm"
include "cr.mm"
include "wss.mm"
include "ciun.mm"
include "wfn.mm"
include "wceq.mm"
include "cvv.mm"
include "wf.mm"
include "cico.mm"
include "reex.mm"
include "fex.mm"
include "sylancl.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffn.mm"
include "fniunfv.mm"
include "wral.mm"
include "cmbf.mm"
include "rge0ssre.mm"
include "fss.mm"
include "mbfima.mm"
include "syl2anc.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "iunmbl.mm"
include "eqeltrrd.mm"
include "mblss.mm"
include "ovolcl.mm"
include "0xr.mm"
include "a1i.mm"
include "mblvol.mm"
include "wrex.mm"
include "sselda.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "syldan.mm"
include "nnrecl.mm"
include "wb.mm"
include "ad2antrr.mm"
include "elpreima.mm"
include "biantrurd.mm"
include "nnrecre.mm"
include "adantl.mm"
include "rexrd.mm"
include "adantlr.mm"
include "elioopnf.mm"
include "3bitr2d.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "imaeq2d.mm"
include "fvmptg.mm"
include "syl2anr.mm"
include "eleq2d.mm"
include "3bitr4rd.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "ex.mm"
include "eluni2.mm"
include "eleq2.mm"
include "rexrn.mm"
include "syl5bb.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "ovolss.mm"
include "eqbrtrd.mm"
include "csup.mm"
include "caddc.mm"
include "peano2nn.mm"
include "nnre.mm"
include "lep1d.mm"
include "nngt0.mm"
include "nnred.mm"
include "nngt0d.mm"
include "lerec.mm"
include "syl22anc.mm"
include "iooss1.mm"
include "imass2.mm"
include "3sstr4d.mm"
include "volsup.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "cif.mm"
include "nnrecgt0.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "0e0iccpnf.mm"
include "ifcl.mm"
include "adantrr.mm"
include "itg2cl.mm"
include "icossicc.mm"
include "crp.mm"
include "0nrp.mm"
include "cmul.mm"
include "simpr.mm"
include "syl6eqelr.mm"
include "elrpd.mm"
include "itg2const2.mm"
include "mpbird.mm"
include "itg2const.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "rpmulcld.mm"
include "eqeltrd.mm"
include "mtoi.mm"
include "wo.mm"
include "itg2ge0.mm"
include "xrleloe.mm"
include "ord.mm"
include "mt3d.mm"
include "cofr.mm"
include "biimpa.mm"
include "simprd.mm"
include "syl6bi.mm"
include "sylc.mm"
include "ltled.mm"
include "breq1.mm"
include "ifboth.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "ovex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvexd.mm"
include "eqidd.mm"
include "feqmptd.mm"
include "ofrfval2.mm"
include "biimpar.mm"
include "itg2le.mm"
include "xrltletrd.mm"
include "expr.mm"
include "con3d.mm"
include "xrlenlt.mm"
include "imp.mm"
include "an32s.mm"
include "fveq2.mm"
include "breq1d.mm"
include "ralrn.mm"
include "3syl.mm"
include "ax-mp.mm"
include "frn.mm"
include "ralima.mm"
include "imassrn.mm"
include "sstri.mm"
include "supxrleub.mm"
include "mp2an.mm"
include "sylibr.mm"
include "xrletrd.mm"
include "sylibd.mm"
include "mt4d.mm"

theorem itg2gt0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  assume itg2gt0.1: |- ( ph -> A e. dom vol )
  assume itg2gt0.2: |- ( ph -> 0 < ( vol ` A ) )
  assume itg2gt0.3: |- ( ph -> F : RR --> ( 0 [,) +oo ) )
  assume itg2gt0.4: |- ( ph -> F e. MblFn )
  assume itg2gt0.5: |- ( ( ph /\ x e. A ) -> 0 < ( F ` x ) )

  disjoint A x
  disjoint F x
  disjoint ph x
  disjoint k x
  disjoint A k
  disjoint k n
  disjoint k z
  disjoint F k
  disjoint n x
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint F z
  disjoint k ph
  disjoint n ph
  assert |- ( ph -> 0 < ( S.2 ` F ) )

  proof
    wph
    cc0
    cA
    cvol
    cfv
    #
    clt
    wbr
    #
    cc0
    cF
    citg2
    cfv
    #
    clt
    wbr
    #
    itg2gt0.2
    wph
    @3
    wn
    #
    @0
    cc0
    cle
    wbr
    #
    @1
    wn
    #
    wph
    @4
    @5
    wph
    @4
    wa
    #
    @0
    vn
    cn
    cF
    ccnv
    #
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cpnf
    cioo
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    cuni
    #
    covol
    cfv
    #
    cc0
    wph
    @0
    cxr
    wcel
    #
    @4
    wph
    cA
    cvol
    cdm
    #
    wcel
    #
    @17
    itg2gt0.1
    @19
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @0
    cc0
    cpnf
    iccssxr
    #
    @18
    @20
    cA
    cvol
    volf
    ffvelrni
    sseldi
    syl
    #
    adantr
    wph
    @16
    cxr
    wcel
    #
    @4
    wph
    @15
    cr
    wss
    #
    @23
    wph
    @15
    @18
    wcel
    #
    @24
    wph
    vk
    cn
    vk
    cv
    #
    @13
    cfv
    #
    ciun
    #
    @15
    @18
    wph
    @13
    cn
    wfn
    #
    @28
    @15
    wceq
    wph
    cn
    cvv
    @13
    wf
    #
    @29
    wph
    vn
    cn
    @12
    cvv
    @13
    wph
    @12
    cvv
    wcel
    #
    @9
    cn
    wcel
    #
    wph
    @8
    cvv
    wcel
    #
    @31
    wph
    cF
    cvv
    wcel
    #
    @33
    wph
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    cr
    cvv
    wcel
    #
    @34
    itg2gt0.3
    reex
    cr
    @35
    cvv
    cF
    fex
    sylancl
    cF
    cvv
    cnvexg
    syl
    #
    @8
    @11
    cvv
    imaexg
    syl
    adantr
    @13
    eqid
    #
    fmptd
    #
    cn
    cvv
    @13
    ffn
    #
    syl
    #
    vk
    cn
    @13
    fniunfv
    syl
    wph
    @27
    @18
    wcel
    #
    vk
    cn
    wral
    @28
    @18
    wcel
    wph
    @43
    vk
    cn
    wph
    cn
    @18
    @26
    @13
    wph
    vn
    cn
    @12
    @18
    @13
    wph
    @12
    @18
    wcel
    #
    @32
    wph
    cF
    cmbf
    wcel
    cr
    cr
    cF
    wf
    #
    @44
    itg2gt0.4
    wph
    @36
    @35
    cr
    wss
    @45
    itg2gt0.3
    rge0ssre
    cr
    @35
    cr
    cF
    fss
    sylancl
    cr
    @10
    cpnf
    cF
    mbfima
    syl2anc
    adantr
    @39
    fmptd
    #
    ffvelrnda
    #
    ralrimiva
    @27
    vk
    iunmbl
    syl
    eqeltrrd
    #
    @15
    mblss
    syl
    #
    @15
    ovolcl
    syl
    adantr
    cc0
    cxr
    wcel
    #
    @7
    0xr
    a1i
    wph
    @0
    @16
    cle
    wbr
    @4
    wph
    @0
    cA
    covol
    cfv
    #
    @16
    cle
    wph
    @19
    @0
    @51
    wceq
    itg2gt0.1
    cA
    mblvol
    syl
    wph
    cA
    @15
    wss
    @24
    @51
    @16
    cle
    wbr
    wph
    vx
    cA
    @15
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @52
    @27
    wcel
    #
    vk
    cn
    wrex
    #
    @52
    @15
    wcel
    #
    wph
    @53
    @55
    wph
    @53
    wa
    #
    c1
    @26
    cdiv
    co
    #
    @52
    cF
    cfv
    #
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    @55
    @57
    @59
    cr
    wcel
    #
    cc0
    @59
    clt
    wbr
    @61
    wph
    @53
    @52
    cr
    wcel
    #
    @62
    wph
    cA
    cr
    @52
    wph
    @19
    cA
    cr
    wss
    itg2gt0.1
    cA
    mblss
    syl
    sselda
    #
    wph
    @63
    wa
    #
    @62
    cc0
    @59
    cle
    wbr
    #
    @65
    @59
    @35
    wcel
    @62
    @66
    wa
    wph
    cr
    @35
    @52
    cF
    itg2gt0.3
    ffvelrnda
    @59
    elrege0
    sylib
    #
    simpld
    #
    syldan
    #
    itg2gt0.5
    @59
    vk
    nnrecl
    syl2anc
    @57
    @60
    @54
    vk
    cn
    @57
    @26
    cn
    wcel
    #
    wa
    #
    @52
    @8
    @58
    cpnf
    cioo
    co
    #
    cima
    #
    wcel
    #
    @62
    @60
    wa
    #
    @54
    @60
    @71
    @74
    @63
    @59
    @72
    wcel
    #
    wa
    #
    @76
    @75
    @71
    cF
    cr
    wfn
    #
    @74
    @77
    wb
    #
    wph
    @78
    @53
    @70
    wph
    @36
    @78
    itg2gt0.3
    cr
    @35
    cF
    ffn
    syl
    #
    ad2antrr
    cr
    @52
    @72
    cF
    elpreima
    #
    syl
    @71
    @63
    @76
    @57
    @63
    @70
    @64
    adantr
    biantrurd
    @71
    @58
    cxr
    wcel
    #
    @76
    @75
    wb
    wph
    @70
    @82
    @53
    wph
    @70
    wa
    #
    @58
    @70
    @58
    cr
    wcel
    #
    wph
    @26
    nnrecre
    adantl
    #
    rexrd
    #
    adantlr
    @58
    @59
    elioopnf
    #
    syl
    3bitr2d
    @71
    @27
    @73
    @52
    @70
    @70
    @73
    cvv
    wcel
    #
    @27
    @73
    wceq
    #
    @57
    @70
    id
    #
    wph
    @88
    @53
    wph
    @33
    @88
    @38
    @8
    @72
    cvv
    imaexg
    syl
    #
    adantr
    vn
    @26
    @12
    @73
    cn
    cvv
    @13
    @9
    @26
    wceq
    #
    @11
    @72
    @8
    @92
    @10
    @58
    cpnf
    cioo
    @9
    @26
    c1
    cdiv
    oveq2
    oveq1d
    imaeq2d
    @39
    fvmptg
    #
    syl2anr
    eleq2d
    @71
    @62
    @60
    @57
    @62
    @70
    @69
    adantr
    biantrurd
    3bitr4rd
    rexbidva
    mpbid
    ex
    @56
    @52
    vz
    cv
    #
    wcel
    #
    vz
    @14
    wrex
    #
    wph
    @55
    vz
    @52
    @14
    eluni2
    wph
    @29
    @96
    @55
    wb
    @42
    @95
    @54
    vz
    vk
    cn
    @13
    @94
    @27
    @52
    eleq2
    rexrn
    syl
    syl5bb
    sylibrd
    ssrdv
    @49
    cA
    @15
    ovolss
    syl2anc
    eqbrtrd
    adantr
    @7
    @16
    cvol
    @14
    cima
    #
    cxr
    clt
    csup
    #
    cc0
    cle
    wph
    @16
    @98
    wceq
    @4
    wph
    @15
    cvol
    cfv
    #
    @16
    @98
    wph
    @25
    @99
    @16
    wceq
    @48
    @15
    mblvol
    syl
    wph
    cn
    @18
    @13
    wf
    #
    @27
    @26
    c1
    caddc
    co
    #
    @13
    cfv
    #
    wss
    #
    vk
    cn
    wral
    @99
    @98
    wceq
    @46
    wph
    @103
    vk
    cn
    @83
    @73
    @8
    c1
    @101
    cdiv
    co
    #
    cpnf
    cioo
    co
    #
    cima
    #
    @27
    @102
    @83
    @72
    @105
    wss
    #
    @73
    @106
    wss
    @83
    @104
    cxr
    wcel
    @104
    @58
    cle
    wbr
    #
    @107
    @83
    @104
    @83
    @101
    cn
    wcel
    #
    @104
    cr
    wcel
    @70
    @109
    wph
    @26
    peano2nn
    #
    adantl
    #
    @101
    nnrecre
    syl
    rexrd
    @83
    @26
    @101
    cle
    wbr
    #
    @108
    @83
    @26
    @70
    @26
    cr
    wcel
    #
    wph
    @26
    nnre
    adantl
    #
    lep1d
    @83
    @113
    cc0
    @26
    clt
    wbr
    #
    @101
    cr
    wcel
    cc0
    @101
    clt
    wbr
    @112
    @108
    wb
    @114
    @70
    @115
    wph
    @26
    nngt0
    adantl
    @83
    @101
    @111
    nnred
    @83
    @101
    @111
    nngt0d
    @26
    @101
    lerec
    syl22anc
    mpbid
    @104
    @58
    cpnf
    iooss1
    syl2anc
    @72
    @105
    @8
    imass2
    syl
    @70
    @70
    @88
    @89
    wph
    @90
    @91
    @93
    syl2anr
    #
    @70
    @109
    @106
    cvv
    wcel
    #
    @102
    @106
    wceq
    wph
    @110
    wph
    @33
    @117
    @38
    @8
    @105
    cvv
    imaexg
    syl
    vn
    @101
    @12
    @106
    cn
    cvv
    @13
    @9
    @101
    wceq
    #
    @11
    @105
    @8
    @118
    @10
    @104
    cpnf
    cioo
    @9
    @101
    c1
    cdiv
    oveq2
    oveq1d
    imaeq2d
    @39
    fvmptg
    syl2anr
    3sstr4d
    ralrimiva
    vk
    @13
    volsup
    syl2anc
    eqtr3d
    adantr
    @7
    @52
    cc0
    cle
    wbr
    #
    vx
    @97
    wral
    #
    @98
    cc0
    cle
    wbr
    #
    @7
    @120
    @94
    cvol
    cfv
    #
    cc0
    cle
    wbr
    #
    vz
    @14
    wral
    #
    @7
    @124
    @27
    cvol
    cfv
    #
    cc0
    cle
    wbr
    #
    vk
    cn
    wral
    #
    @7
    @126
    vk
    cn
    @7
    @70
    wa
    #
    @125
    @73
    cvol
    cfv
    #
    cc0
    cle
    @128
    @27
    @73
    cvol
    @70
    @70
    @88
    @89
    @7
    @90
    wph
    @88
    @4
    @91
    adantr
    @93
    syl2anr
    fveq2d
    wph
    @70
    @4
    @129
    cc0
    cle
    wbr
    #
    @83
    @4
    @130
    @83
    @4
    cc0
    @129
    clt
    wbr
    #
    wn
    #
    @130
    @83
    @131
    @3
    wph
    @70
    @131
    @3
    wph
    @70
    @131
    wa
    #
    wa
    #
    cc0
    vx
    cr
    @74
    @58
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    @2
    @50
    @134
    0xr
    a1i
    @134
    cr
    @20
    @136
    wf
    #
    @137
    cxr
    wcel
    #
    wph
    @70
    @138
    @131
    @83
    vx
    cr
    @135
    @20
    @136
    @83
    @135
    @20
    wcel
    #
    @63
    @83
    @58
    @20
    wcel
    #
    cc0
    @20
    wcel
    @140
    @83
    @82
    cc0
    @58
    cle
    wbr
    #
    @141
    @86
    @83
    cc0
    @58
    clt
    wbr
    #
    @142
    @70
    @143
    wph
    @26
    nnrecgt0
    adantl
    #
    @83
    cc0
    cr
    wcel
    @84
    @143
    @142
    wi
    0re
    @85
    cc0
    @58
    ltle
    sylancr
    mpd
    #
    @58
    elxrge0
    sylanbrc
    0e0iccpnf
    @74
    @58
    cc0
    @20
    ifcl
    sylancl
    adantr
    @136
    eqid
    fmptd
    adantrr
    #
    @136
    itg2cl
    syl
    #
    wph
    @2
    cxr
    wcel
    #
    @133
    wph
    cr
    @20
    cF
    wf
    #
    @148
    wph
    @36
    @35
    @20
    wss
    @149
    itg2gt0.3
    cc0
    cpnf
    icossicc
    cr
    @35
    @20
    cF
    fss
    sylancl
    #
    cF
    itg2cl
    syl
    adantr
    @134
    cc0
    @137
    clt
    wbr
    #
    cc0
    @137
    wceq
    #
    @134
    @152
    cc0
    crp
    wcel
    #
    0nrp
    @134
    @152
    @153
    @134
    @152
    wa
    #
    cc0
    @58
    @129
    cmul
    co
    #
    crp
    @154
    cc0
    @137
    @155
    @134
    @152
    simpr
    #
    @154
    @73
    @18
    wcel
    #
    @129
    cr
    wcel
    #
    @58
    @35
    wcel
    #
    @137
    @155
    wceq
    @134
    @157
    @152
    wph
    @70
    @157
    @131
    @83
    @27
    @73
    @18
    @116
    @47
    eqeltrrd
    #
    adantrr
    adantr
    #
    @154
    @158
    @137
    cr
    wcel
    #
    @154
    @137
    cc0
    cr
    @156
    0re
    syl6eqelr
    @154
    @157
    @58
    crp
    wcel
    #
    @158
    @162
    wb
    @161
    @134
    @163
    @152
    wph
    @70
    @163
    @131
    @83
    @58
    @85
    @144
    elrpd
    adantrr
    adantr
    #
    vx
    @73
    @58
    itg2const2
    syl2anc
    mpbird
    #
    @134
    @159
    @152
    wph
    @70
    @159
    @131
    @83
    @84
    @142
    @159
    @85
    @145
    @58
    elrege0
    sylanbrc
    adantrr
    adantr
    vx
    @73
    @58
    itg2const
    syl3anc
    eqtrd
    @154
    @58
    @129
    @164
    @154
    @129
    @165
    wph
    @70
    @131
    @152
    simplrr
    elrpd
    rpmulcld
    eqeltrd
    ex
    mtoi
    @134
    @151
    @152
    @134
    cc0
    @137
    cle
    wbr
    #
    @151
    @152
    wo
    #
    @134
    @138
    @166
    @146
    @136
    itg2ge0
    syl
    @134
    @50
    @139
    @166
    @167
    wb
    0xr
    @147
    cc0
    @137
    xrleloe
    sylancr
    mpbid
    ord
    mt3d
    @134
    @138
    @149
    @136
    cF
    cle
    cofr
    wbr
    #
    @137
    @2
    cle
    wbr
    @146
    wph
    @149
    @133
    @150
    adantr
    wph
    @133
    @135
    @59
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @168
    wph
    @70
    @170
    @131
    @83
    @169
    vx
    cr
    @83
    @63
    wa
    #
    @74
    @169
    @83
    @74
    @169
    @63
    @83
    @74
    wa
    #
    @58
    @59
    cle
    wbr
    #
    @66
    @169
    @172
    @58
    @59
    @83
    @84
    @74
    @85
    adantr
    @83
    @74
    @63
    @62
    @172
    @63
    @76
    @83
    @74
    @77
    @83
    @78
    @79
    wph
    @78
    @70
    @80
    adantr
    @81
    syl
    biimpa
    #
    simpld
    #
    wph
    @63
    @62
    @70
    @68
    adantlr
    syldan
    @172
    @82
    @76
    @60
    @83
    @82
    @74
    @86
    adantr
    @172
    @63
    @76
    @174
    simprd
    @82
    @76
    @75
    @60
    @87
    @62
    @60
    simpr
    syl6bi
    sylc
    ltled
    @83
    @74
    @63
    @66
    @175
    wph
    @63
    @66
    @70
    @65
    @62
    @66
    @67
    simprd
    adantlr
    #
    syldan
    @74
    @173
    @66
    @169
    @58
    cc0
    @58
    @135
    @59
    cle
    breq1
    cc0
    @135
    @59
    cle
    breq1
    ifboth
    syl2anc
    adantlr
    @171
    @74
    wn
    #
    wa
    @135
    cc0
    @59
    cle
    @177
    @135
    cc0
    wceq
    @171
    @74
    @58
    cc0
    iffalse
    adantl
    @171
    @66
    @177
    @176
    adantr
    eqbrtrd
    pm2.61dan
    ralrimiva
    adantrr
    wph
    @168
    @170
    wph
    vx
    cr
    @135
    @59
    cle
    @136
    cF
    cvv
    cvv
    cvv
    @37
    wph
    reex
    a1i
    @135
    cvv
    wcel
    @65
    @74
    @58
    cc0
    c1
    @26
    cdiv
    ovex
    c0ex
    ifex
    a1i
    @65
    @52
    cF
    fvexd
    wph
    @136
    eqidd
    wph
    vx
    cr
    @35
    cF
    itg2gt0.3
    feqmptd
    ofrfval2
    biimpar
    syldan
    @136
    cF
    itg2le
    syl3anc
    xrltletrd
    expr
    con3d
    @83
    @129
    cxr
    wcel
    #
    @50
    @130
    @132
    wb
    @83
    @157
    @178
    @160
    @157
    @20
    cxr
    @129
    @21
    @18
    @20
    @73
    cvol
    volf
    ffvelrni
    sseldi
    syl
    0xr
    @129
    cc0
    xrlenlt
    sylancl
    sylibrd
    imp
    an32s
    eqbrtrd
    ralrimiva
    wph
    @124
    @127
    wb
    #
    @4
    wph
    @30
    @29
    @179
    @40
    @41
    @123
    @126
    vz
    vk
    cn
    @13
    @94
    @27
    wceq
    @122
    @125
    cc0
    cle
    @94
    @27
    cvol
    fveq2
    breq1d
    ralrn
    3syl
    adantr
    mpbird
    @7
    cvol
    @18
    wfn
    #
    @14
    @18
    wss
    #
    @120
    @124
    wb
    @18
    @20
    cvol
    wf
    #
    @180
    volf
    @18
    @20
    cvol
    ffn
    ax-mp
    wph
    @181
    @4
    wph
    @100
    @181
    @46
    cn
    @18
    @13
    frn
    syl
    adantr
    @119
    @123
    vx
    vz
    @18
    @14
    cvol
    @52
    @122
    cc0
    cle
    breq1
    ralima
    sylancr
    mpbird
    @97
    cxr
    wss
    @50
    @121
    @120
    wb
    @97
    cvol
    crn
    #
    cxr
    cvol
    @14
    imassrn
    @183
    @20
    cxr
    @182
    @183
    @20
    wss
    volf
    @18
    @20
    cvol
    frn
    ax-mp
    @21
    sstri
    sstri
    0xr
    vx
    @97
    cc0
    supxrleub
    mp2an
    sylibr
    eqbrtrd
    xrletrd
    ex
    wph
    @17
    @50
    @5
    @6
    wb
    @22
    0xr
    @0
    cc0
    xrlenlt
    sylancl
    sylibd
    mt4d
end
