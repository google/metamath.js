include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cv.mm"
include "cesum.mm"
include "cmpt.mm"
include "cgsu.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "wceq.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfan.mm"
include "cle.mm"
include "wss.mm"
include "iccssxr.mm"
include "xrge0base.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "simpr.mm"
include "elin2d.mm"
include "simpll.mm"
include "elin1d.mm"
include "adantr.mm"
include "vex.mm"
include "elpw.mm"
include "sylib.mm"
include "sseldd.mm"
include "nfiu1.mm"
include "cop.mm"
include "adantl.mm"
include "simp-5l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "syl12anc.mm"
include "eqeltrd.mm"
include "elsnxp.mm"
include "biimpa.mm"
include "adantll.mm"
include "r19.29af2.mm"
include "eliun.mm"
include "r19.29af.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "sseldi.mm"
include "eqid.mm"
include "rnmptss.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "cvv.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancr.mm"
include "iunexg.mm"
include "esumcl.mm"
include "esumgsum.mm"
include "adantlr.mm"
include "esummono.mm"
include "eqbrtrrd.mm"
include "eqbrtrd.mm"
include "xrlenlt.mm"
include "syl21anc.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "nfrex.mm"
include "elrnmpt1.mm"
include "breq2d.mm"
include "rspcedvd.mm"
include "nfesum1.mm"
include "nfbr.mm"
include "ad2antrr.mm"
include "3ad2antr3.mm"
include "3anassrs.mm"
include "esumlub.mm"
include "ex.mm"
include "jca.mm"
include "breq1d.mm"
include "notbid.mm"
include "ralbidv.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "rspcedv.mm"
include "mpd.mm"
include "supcl.mm"
include "elpwi.mm"
include "sselda.mm"
include "adantrr.mm"
include "simprr.mm"
include "esum2dlem.mm"
include "anassrs.mm"
include "eqtr3d.mm"
include "iunss1.mm"
include "wb.mm"
include "mpbid.mm"
include "eqidd.mm"
include "esumval.mm"
include "mtbid.mm"
include "mpbird.mm"
include "biimpi.mm"
include "nfel1.mm"
include "nfsup.mm"
include "w3a.mm"
include "simpr1l.mm"
include "simpr1r.mm"
include "breqtrd.mm"
include "cdm.mm"
include "dmss.mm"
include "dmiun.mm"
include "syl6sseq.mm"
include "dmxpss.mm"
include "snssi.mm"
include "sstrd.mm"
include "rgen.mm"
include "iunss.mm"
include "mpbir.mm"
include "syl6ss.mm"
include "dmex.mm"
include "sylibr.mm"
include "3syl.mm"
include "dmfi.mm"
include "elind.mm"
include "mpteq1.mm"
include "oveq2d.mm"
include "elrnmpt1s.mm"
include "nfov.mm"
include "simp-4l.mm"
include "ralrimi.mm"
include "nfpw.mm"
include "nfin.mm"
include "adantllr.mm"
include "cima.mm"
include "wrel.mm"
include "id.mm"
include "xpss.mm"
include "rgenw.mm"
include "df-rel.mm"
include "gsummpt2d.mm"
include "imass1.mm"
include "iunsnima.mm"
include "sseqtrd.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "mpan.mm"
include "esumlef.mm"
include "imafi2.mm"
include "mpteq2da.mm"
include "eqtrd.mm"
include "3brtr3d.mm"
include "xrltletrd.mm"
include "ad2antlr.mm"
include "suplub.mm"
include "imp.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "r19.29a.mm"
include "eqsupd.mm"
include "3eqtr4d.mm"

theorem esum2d
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vl: setvar l
  let vt: setvar t
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  assume esum2d.0: |- F/_ k F
  assume esum2d.1: |- ( z = <. j , k >. -> F = C )
  assume esum2d.2: |- ( ph -> A e. V )
  assume esum2d.3: |- ( ( ph /\ j e. A ) -> B e. W )
  assume esum2d.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. ( 0 [,] +oo ) )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint A z
  disjoint j z
  disjoint k z
  disjoint C z
  disjoint B k
  disjoint B z
  disjoint F j
  disjoint W j
  disjoint W k
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i t
  disjoint j l
  disjoint j t
  disjoint k l
  disjoint k t
  disjoint l t
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A l
  disjoint A r
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint a b
  disjoint a c
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a z
  disjoint b c
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b z
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c z
  disjoint j r
  disjoint j s
  disjoint j u
  disjoint k r
  disjoint k s
  disjoint k u
  disjoint l r
  disjoint l s
  disjoint l u
  disjoint l z
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r z
  disjoint s t
  disjoint s u
  disjoint s z
  disjoint t u
  disjoint t z
  disjoint u z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C l
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B i
  disjoint B l
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint a i
  disjoint b i
  disjoint c i
  disjoint i r
  disjoint i s
  disjoint i u
  disjoint i z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F l
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint l ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  assert |- ( ph -> sum* j e. A sum* k e. B C = sum* z e. U_ j e. A ( { j } X. B ) F )

  proof
    wph
    va
    cA
    cpw
    #
    cfn
    cin
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vj
    va
    cv
    #
    cB
    cC
    vk
    cesum
    #
    cmpt
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
    vc
    vj
    cA
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    cpw
    #
    cfn
    cin
    #
    @3
    vz
    vc
    cv
    #
    cF
    cmpt
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
    cA
    @5
    vj
    cesum
    @13
    cF
    vz
    cesum
    #
    wph
    vs
    vt
    cxr
    @9
    @21
    clt
    cxr
    clt
    wor
    wph
    xrltso
    a1i
    #
    wph
    vr
    vs
    vt
    cxr
    @20
    clt
    @23
    wph
    @22
    vs
    cv
    #
    clt
    wbr
    #
    wn
    #
    vs
    @20
    wral
    #
    @24
    @22
    clt
    wbr
    #
    @24
    vt
    cv
    #
    clt
    wbr
    #
    vt
    @20
    wrex
    #
    wi
    #
    vs
    cxr
    wral
    #
    wa
    #
    vr
    cv
    #
    @24
    clt
    wbr
    #
    wn
    #
    vs
    @20
    wral
    #
    @24
    @35
    clt
    wbr
    #
    @31
    wi
    #
    vs
    cxr
    wral
    #
    wa
    #
    vr
    cxr
    wrex
    wph
    @27
    @33
    wph
    @26
    vs
    @20
    wph
    @24
    @20
    wcel
    #
    wa
    #
    @24
    @18
    wceq
    #
    @26
    vc
    @15
    wph
    @43
    vc
    wph
    vc
    nfv
    #
    vc
    @24
    @20
    vc
    @24
    nfcv
    #
    vc
    @19
    vc
    @15
    @18
    nfmpt1
    nfrn
    #
    nfel
    nfan
    @44
    @16
    @15
    wcel
    #
    wa
    #
    @45
    wa
    #
    @24
    cxr
    wcel
    #
    @22
    cxr
    wcel
    #
    @24
    @22
    cle
    wbr
    #
    @26
    @51
    @20
    cxr
    @24
    wph
    @20
    cxr
    wss
    #
    @43
    @49
    @45
    wph
    @18
    cxr
    wcel
    #
    vc
    @15
    wral
    @55
    wph
    @56
    vc
    @15
    wph
    @49
    wa
    #
    @2
    cxr
    @18
    cc0
    cpnf
    iccssxr
    #
    @57
    @2
    vz
    @3
    @16
    cF
    xrge0base
    @3
    ccmn
    wcel
    #
    @57
    xrge0cmn
    a1i
    #
    @57
    @14
    cfn
    @16
    wph
    @49
    simpr
    #
    elin2d
    #
    @57
    cF
    @2
    wcel
    #
    vz
    @16
    @57
    vz
    cv
    #
    @16
    wcel
    #
    wa
    #
    wph
    @64
    @13
    wcel
    #
    @63
    wph
    @49
    @65
    simpll
    @66
    @16
    @13
    @64
    @66
    @16
    @14
    wcel
    #
    @16
    @13
    wss
    #
    @57
    @68
    @65
    @57
    @14
    cfn
    @16
    @61
    elin1d
    #
    adantr
    @16
    @13
    vc
    vex
    #
    elpw
    #
    sylib
    @57
    @65
    simpr
    sseldd
    wph
    @67
    wa
    #
    @64
    @12
    wcel
    #
    @63
    vj
    cA
    wph
    @67
    vj
    wph
    vj
    nfv
    #
    vj
    @64
    @13
    vj
    @64
    nfcv
    vj
    cA
    @12
    nfiu1
    #
    nfel
    nfan
    @73
    @10
    cA
    wcel
    #
    wa
    @74
    wa
    #
    @64
    @10
    vk
    cv
    #
    cop
    wceq
    #
    @63
    vk
    cB
    @78
    vk
    nfv
    vk
    cF
    @2
    esum2d.0
    vk
    @2
    nfcv
    nfel
    @78
    @79
    cB
    wcel
    #
    wa
    #
    @80
    wa
    #
    cF
    cC
    @2
    @80
    cF
    cC
    wceq
    @82
    esum2d.1
    adantl
    @83
    wph
    @77
    @81
    cC
    @2
    wcel
    #
    wph
    @67
    @77
    @74
    @81
    @80
    simp-5l
    @73
    @77
    @74
    @81
    @80
    simp-4r
    @78
    @81
    @80
    simplr
    esum2d.4
    syl12anc
    eqeltrd
    @77
    @74
    @80
    vk
    cB
    wrex
    #
    @73
    @77
    @74
    @85
    vk
    cB
    cA
    @10
    @64
    elsnxp
    biimpa
    adantll
    r19.29af2
    @73
    @67
    @74
    vj
    cA
    wrex
    wph
    @67
    simpr
    vj
    @64
    cA
    @12
    eliun
    sylib
    r19.29af
    #
    syl2anc
    #
    ralrimiva
    gsummptcl
    sseldi
    ralrimiva
    vc
    @15
    @18
    cxr
    @19
    @19
    eqid
    #
    rnmptss
    syl
    ad3antrrr
    wph
    @43
    @49
    @45
    simpllr
    sseldd
    wph
    @53
    @43
    @49
    @45
    wph
    @2
    cxr
    @22
    @58
    wph
    @13
    cvv
    wcel
    #
    @63
    vz
    @13
    wral
    @22
    @2
    wcel
    wph
    cA
    cV
    wcel
    @12
    cvv
    wcel
    #
    vj
    cA
    wral
    @89
    esum2d.2
    wph
    @90
    vj
    cA
    wph
    @77
    wa
    #
    @11
    cvv
    wcel
    cB
    cW
    wcel
    #
    @90
    @10
    snex
    esum2d.3
    @11
    cB
    cvv
    cW
    xpexg
    sylancr
    ralrimiva
    vj
    cA
    @12
    cV
    cvv
    iunexg
    syl2anc
    #
    wph
    @63
    vz
    @13
    @86
    ralrimiva
    @13
    cF
    vz
    cvv
    vz
    @13
    nfcv
    #
    esumcl
    syl2anc
    sseldi
    #
    ad3antrrr
    @51
    @24
    @18
    @22
    cle
    @50
    @45
    simpr
    @50
    @18
    @22
    cle
    wbr
    #
    @45
    wph
    @49
    @96
    @43
    @57
    @16
    cF
    vz
    cesum
    #
    @18
    @22
    cle
    @57
    @16
    cF
    vz
    @57
    vz
    nfv
    #
    vz
    @16
    nfcv
    @62
    @87
    esumgsum
    #
    @57
    @16
    cF
    @13
    vz
    cvv
    @98
    wph
    @89
    @49
    @93
    adantr
    wph
    @67
    @63
    @49
    @86
    adantlr
    @57
    @68
    @69
    @70
    @72
    sylib
    #
    esummono
    eqbrtrrd
    adantlr
    adantr
    eqbrtrd
    @52
    @53
    wa
    @54
    @26
    @24
    @22
    xrlenlt
    biimpa
    syl21anc
    @44
    @43
    @45
    vc
    @15
    wrex
    wph
    @43
    simpr
    vc
    @15
    @18
    @24
    @19
    @88
    @3
    @17
    cgsu
    ovex
    #
    elrnmpti
    sylib
    r19.29af
    ralrimiva
    wph
    @32
    vs
    cxr
    wph
    @52
    wa
    #
    @28
    @31
    @102
    @28
    wa
    #
    @24
    @97
    clt
    wbr
    #
    @31
    vc
    @15
    @103
    vc
    nfv
    @30
    vc
    vt
    @20
    @48
    @30
    vc
    nfv
    nfrex
    @103
    @49
    wa
    #
    @104
    wa
    #
    @30
    @104
    vt
    @97
    @20
    @106
    @97
    @18
    @20
    @105
    @97
    @18
    wceq
    #
    @104
    @102
    @49
    @107
    @28
    wph
    @49
    @107
    @52
    @99
    adantlr
    adantlr
    adantr
    @106
    @49
    @18
    cvv
    wcel
    #
    @18
    @20
    wcel
    @103
    @49
    @104
    simplr
    @108
    @106
    @101
    a1i
    vc
    @15
    @18
    @19
    cvv
    @88
    elrnmpt1
    syl2anc
    eqeltrd
    @106
    @29
    @97
    wceq
    #
    wa
    @29
    @97
    @24
    clt
    @106
    @109
    simpr
    breq2d
    @105
    @104
    simpr
    rspcedvd
    @103
    @13
    cF
    vz
    cvv
    @24
    vc
    @102
    @28
    vz
    @102
    vz
    nfv
    #
    vz
    @24
    @22
    clt
    vz
    @24
    nfcv
    #
    vz
    clt
    nfcv
    #
    @13
    cF
    vz
    @94
    nfesum1
    nfbr
    nfan
    wph
    @89
    @52
    @28
    @93
    ad2antrr
    wph
    @52
    @28
    @67
    @63
    wph
    @52
    @67
    @63
    @28
    @86
    3ad2antr3
    3anassrs
    wph
    @52
    @28
    simplr
    @102
    @28
    simpr
    esumlub
    r19.29af2
    ex
    ralrimiva
    jca
    wph
    @42
    @34
    vr
    @22
    cxr
    @95
    wph
    @35
    @22
    wceq
    #
    wa
    #
    @38
    @27
    @41
    @33
    @114
    @37
    @26
    vs
    @20
    @114
    @36
    @25
    @114
    @35
    @22
    @24
    clt
    wph
    @113
    simpr
    #
    breq1d
    notbid
    ralbidv
    @114
    @40
    @32
    vs
    cxr
    @114
    @39
    @28
    @31
    @114
    @35
    @22
    @24
    clt
    @115
    breq2d
    imbi1d
    ralbidv
    anbi12d
    rspcedv
    mpd
    #
    supcl
    wph
    @24
    @9
    wcel
    #
    wa
    #
    @24
    @7
    wceq
    #
    @21
    @24
    clt
    wbr
    #
    wn
    #
    va
    @1
    wph
    @117
    va
    wph
    va
    nfv
    va
    @24
    @9
    va
    @24
    nfcv
    va
    @8
    va
    @1
    @7
    nfmpt1
    nfrn
    nfel
    nfan
    @118
    @4
    @1
    wcel
    #
    wa
    #
    @119
    wa
    #
    @121
    @21
    @7
    clt
    wbr
    #
    wn
    #
    @123
    @126
    @119
    wph
    @122
    @126
    @117
    wph
    @122
    wa
    #
    @22
    @7
    clt
    wbr
    #
    @125
    @127
    @7
    @22
    cle
    wbr
    #
    @128
    wn
    #
    @127
    vj
    @4
    @12
    ciun
    #
    cF
    vz
    cesum
    #
    @7
    @22
    cle
    @127
    @4
    @5
    vj
    cesum
    @132
    @7
    @127
    vz
    @4
    cB
    cC
    vj
    vk
    cF
    @1
    cW
    esum2d.0
    esum2d.1
    wph
    @122
    simpr
    #
    @127
    @10
    @4
    wcel
    #
    wa
    #
    wph
    @77
    @92
    wph
    @122
    @134
    simpll
    #
    @127
    @4
    cA
    @10
    @127
    @4
    @0
    wcel
    @4
    cA
    wss
    #
    @127
    @0
    cfn
    @4
    @133
    elin1d
    @4
    cA
    elpwi
    syl
    #
    sselda
    #
    esum2d.3
    syl2anc
    @127
    @134
    @81
    wa
    wa
    wph
    @77
    @81
    @84
    @127
    @134
    wph
    @81
    @136
    adantrr
    @127
    @134
    @77
    @81
    @139
    adantrr
    @127
    @134
    @81
    simprr
    esum2d.4
    syl12anc
    @127
    @0
    cfn
    @4
    @133
    elin2d
    #
    esum2dlem
    @127
    @4
    @5
    vj
    @127
    vj
    nfv
    vj
    @4
    nfcv
    @140
    @135
    wph
    @77
    @5
    @2
    wcel
    #
    @136
    @139
    @91
    @92
    @84
    vk
    cB
    wral
    @141
    esum2d.3
    @91
    @84
    vk
    cB
    wph
    @77
    @81
    @84
    esum2d.4
    anassrs
    ralrimiva
    cB
    cC
    vk
    cW
    vk
    cB
    nfcv
    esumcl
    syl2anc
    #
    syl2anc
    #
    esumgsum
    eqtr3d
    @127
    @131
    cF
    @13
    vz
    cvv
    @127
    vz
    nfv
    wph
    @89
    @122
    @93
    adantr
    wph
    @67
    @63
    @122
    @86
    adantlr
    @127
    @137
    @131
    @13
    wss
    @138
    vj
    @4
    cA
    @12
    iunss1
    syl
    esummono
    eqbrtrrd
    @127
    @7
    cxr
    wcel
    @53
    @129
    @130
    wb
    @127
    @2
    cxr
    @7
    @58
    @127
    @2
    vj
    @3
    @4
    @5
    xrge0base
    @59
    @127
    xrge0cmn
    a1i
    @140
    @127
    @141
    vj
    @4
    @143
    ralrimiva
    gsummptcl
    sseldi
    wph
    @53
    @122
    @95
    adantr
    @7
    @22
    xrlenlt
    syl2anc
    mpbid
    @127
    @22
    @21
    @7
    clt
    wph
    @22
    @21
    wceq
    @122
    wph
    vc
    @13
    cF
    @18
    vz
    cvv
    wph
    vz
    nfv
    @94
    @93
    @86
    @57
    @18
    eqidd
    esumval
    #
    adantr
    breq1d
    mtbid
    adantlr
    adantr
    @124
    @120
    @125
    @124
    @24
    @7
    @21
    clt
    @123
    @119
    simpr
    breq2d
    notbid
    mpbird
    @117
    @119
    va
    @1
    wrex
    #
    wph
    @117
    @145
    va
    @1
    @7
    @24
    @8
    @8
    eqid
    #
    @3
    @6
    cgsu
    ovex
    elrnmpti
    biimpi
    adantl
    r19.29af
    wph
    @52
    @24
    @21
    clt
    wbr
    #
    wa
    #
    wa
    #
    @24
    vu
    cv
    #
    clt
    wbr
    #
    @30
    vt
    @9
    wrex
    #
    vu
    @20
    @149
    @150
    @20
    wcel
    #
    wa
    #
    @151
    wa
    #
    @150
    @18
    wceq
    #
    @152
    vc
    @15
    @154
    @151
    vc
    @149
    @153
    vc
    wph
    @148
    vc
    @46
    @52
    @147
    vc
    vc
    @24
    cxr
    @47
    nfel1
    vc
    @24
    @21
    clt
    @47
    vc
    clt
    nfcv
    #
    vc
    @20
    cxr
    clt
    @48
    vc
    cxr
    nfcv
    @157
    nfsup
    nfbr
    nfan
    nfan
    vc
    @150
    @20
    vc
    @150
    nfcv
    @48
    nfel
    nfan
    @151
    vc
    nfv
    nfan
    @155
    @49
    wa
    #
    @156
    wa
    #
    @102
    @147
    wa
    @24
    @18
    clt
    wbr
    #
    @49
    @152
    @159
    @102
    @147
    @159
    wph
    @52
    wph
    @148
    @153
    @151
    @49
    @156
    simp-5l
    @154
    @151
    @49
    @156
    @52
    wph
    @148
    @153
    @151
    @49
    @156
    w3a
    #
    @52
    @52
    @147
    @153
    @161
    wph
    simpr1l
    3anassrs
    3anassrs
    jca
    @154
    @151
    @49
    @156
    @147
    wph
    @148
    @153
    @161
    @147
    @52
    @147
    @153
    @161
    wph
    simpr1r
    3anassrs
    3anassrs
    jca
    @159
    @24
    @150
    @18
    clt
    @154
    @151
    @49
    @156
    simpllr
    @158
    @156
    simpr
    breqtrd
    @155
    @49
    @156
    simplr
    @102
    @160
    @49
    @152
    @147
    @102
    @160
    wa
    #
    @49
    wa
    #
    @30
    @24
    @3
    vj
    @16
    cdm
    #
    @5
    cmpt
    #
    cgsu
    co
    #
    clt
    wbr
    vt
    @166
    @9
    @163
    @164
    @1
    wcel
    @166
    cvv
    wcel
    #
    @166
    @9
    wcel
    @163
    @0
    cfn
    @164
    @163
    @68
    @69
    @164
    @0
    wcel
    #
    @163
    @14
    cfn
    @16
    @162
    @49
    simpr
    #
    elin1d
    #
    @16
    @13
    elpwi
    #
    @69
    @164
    cA
    wss
    #
    @168
    @69
    @164
    vj
    cA
    @12
    cdm
    #
    ciun
    #
    cA
    @69
    @164
    @13
    cdm
    @174
    @16
    @13
    dmss
    vj
    cA
    @12
    dmiun
    syl6sseq
    @174
    cA
    wss
    @173
    cA
    wss
    #
    vj
    cA
    wral
    @175
    vj
    cA
    @77
    @173
    @11
    cA
    @173
    @11
    wss
    @77
    @11
    cB
    dmxpss
    a1i
    @10
    cA
    snssi
    sstrd
    rgen
    vj
    cA
    @173
    cA
    iunss
    mpbir
    syl6ss
    #
    @164
    cA
    @16
    @71
    dmex
    #
    elpw
    sylibr
    3syl
    @163
    @16
    cfn
    wcel
    #
    @164
    cfn
    wcel
    #
    @163
    @14
    cfn
    @16
    @169
    elin2d
    #
    @16
    dmfi
    #
    syl
    #
    elind
    @167
    @163
    @3
    @165
    cgsu
    ovex
    a1i
    va
    @1
    @7
    @166
    @164
    @8
    cvv
    @146
    @4
    @164
    wceq
    @6
    @165
    @3
    cgsu
    vj
    @4
    @164
    @5
    mpteq1
    oveq2d
    elrnmpt1s
    syl2anc
    @163
    @29
    @166
    wceq
    #
    wa
    @29
    @166
    @24
    clt
    @163
    @183
    simpr
    breq2d
    @163
    @24
    @18
    @166
    wph
    @52
    @160
    @49
    simpllr
    @163
    @2
    cxr
    @18
    @58
    @163
    @2
    vz
    @3
    @16
    cF
    xrge0base
    @59
    @163
    xrge0cmn
    a1i
    #
    @180
    @163
    @63
    vz
    @16
    @162
    @49
    vz
    @102
    @160
    vz
    @110
    vz
    @24
    @18
    clt
    @111
    @112
    vz
    @3
    @17
    cgsu
    vz
    @3
    nfcv
    vz
    cgsu
    nfcv
    vz
    @16
    cF
    nfmpt1
    nfov
    nfbr
    nfan
    @49
    vz
    nfv
    nfan
    @163
    @65
    @63
    @163
    @65
    wa
    wph
    @67
    @63
    wph
    @52
    @160
    @49
    @65
    simp-4l
    @163
    @16
    @13
    @64
    @163
    @68
    @69
    @170
    @171
    syl
    sselda
    @86
    syl2anc
    ex
    ralrimi
    gsummptcl
    sseldi
    @163
    @2
    cxr
    @166
    @58
    @163
    @2
    vj
    @3
    @164
    @5
    xrge0base
    @184
    @182
    @163
    @141
    vj
    @164
    @162
    @49
    vj
    @162
    vj
    nfv
    vj
    @16
    @15
    vj
    @16
    nfcv
    vj
    @14
    cfn
    vj
    @13
    @76
    nfpw
    vj
    cfn
    nfcv
    nfin
    nfel
    #
    nfan
    @163
    @10
    @164
    wcel
    #
    @141
    @102
    @49
    @186
    @141
    @160
    wph
    @49
    @186
    @141
    @52
    @57
    @186
    wa
    #
    wph
    @77
    @141
    wph
    @49
    @186
    simpll
    #
    @57
    @164
    cA
    @10
    @57
    @69
    @172
    @100
    @176
    syl
    sselda
    #
    @142
    syl2anc
    #
    adantllr
    adantllr
    ex
    ralrimi
    gsummptcl
    sseldi
    @102
    @160
    @49
    simplr
    @102
    @49
    @18
    @166
    cle
    wbr
    #
    @160
    wph
    @49
    @191
    @52
    @57
    @18
    @3
    vj
    @164
    @3
    vk
    @16
    @11
    cima
    #
    cC
    cmpt
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @166
    cle
    @57
    vz
    vj
    vk
    @16
    @2
    cF
    cC
    @3
    esum2d.0
    wph
    @49
    vj
    @75
    @185
    nfan
    #
    xrge0base
    esum2d.1
    @57
    @16
    cvv
    cvv
    cxp
    #
    wss
    #
    @16
    wrel
    @57
    @69
    @198
    @100
    @69
    @16
    @13
    @197
    @69
    id
    @13
    @197
    wss
    #
    @69
    @199
    @12
    @197
    wss
    #
    vj
    cA
    wral
    @200
    vj
    cA
    @11
    cB
    xpss
    rgenw
    vj
    cA
    @12
    @197
    iunss
    mpbir
    a1i
    sstrd
    syl
    @16
    df-rel
    sylibr
    @62
    @60
    @87
    gsummpt2d
    @57
    @164
    @192
    cC
    vk
    cesum
    #
    vj
    cesum
    #
    @164
    @5
    vj
    cesum
    @195
    @166
    cle
    @57
    @164
    @201
    @5
    vj
    cvv
    @196
    vj
    @164
    nfcv
    #
    @164
    cvv
    wcel
    @57
    @177
    a1i
    @187
    @84
    vk
    @192
    wral
    #
    @201
    @2
    wcel
    #
    @187
    @84
    vk
    @192
    @187
    @79
    @192
    wcel
    #
    wa
    wph
    @77
    @81
    @84
    @187
    wph
    @206
    @188
    adantr
    @187
    @77
    @206
    @189
    adantr
    @187
    @192
    cB
    @79
    @187
    @192
    @13
    @11
    cima
    #
    cB
    @187
    @69
    @192
    @207
    wss
    @57
    @69
    @186
    @100
    adantr
    @16
    @13
    @11
    imass1
    syl
    @187
    wph
    @77
    @207
    cB
    wceq
    @188
    @189
    wph
    vj
    cA
    cB
    cV
    cW
    esum2d.2
    esum2d.3
    iunsnima
    syl2anc
    sseqtrd
    #
    sselda
    esum2d.4
    syl12anc
    #
    ralrimiva
    @192
    cvv
    wcel
    #
    @204
    @205
    @16
    cvv
    wcel
    @210
    @71
    @16
    @11
    cvv
    imaexg
    ax-mp
    @192
    cC
    vk
    cvv
    vk
    @192
    nfcv
    #
    esumcl
    mpan
    syl
    #
    @190
    @187
    @192
    cC
    cB
    vk
    cW
    @187
    vk
    nfv
    #
    @187
    wph
    @77
    @92
    @188
    @189
    esum2d.3
    syl2anc
    @187
    @81
    wa
    wph
    @77
    @81
    @84
    @187
    wph
    @81
    @188
    adantr
    @187
    @77
    @81
    @189
    adantr
    @187
    @81
    simpr
    esum2d.4
    syl12anc
    @208
    esummono
    esumlef
    @57
    @202
    @3
    vj
    @164
    @201
    cmpt
    #
    cgsu
    co
    @195
    @57
    @164
    @201
    vj
    @196
    @203
    @57
    @178
    @179
    @62
    @181
    syl
    #
    @212
    esumgsum
    @57
    @214
    @194
    @3
    cgsu
    @57
    vj
    @164
    @201
    @193
    @196
    @187
    @192
    cC
    vk
    @213
    @211
    @187
    @178
    @192
    cfn
    wcel
    @57
    @178
    @186
    @62
    adantr
    @16
    @11
    imafi2
    syl
    @209
    esumgsum
    mpteq2da
    oveq2d
    eqtrd
    @57
    @164
    @5
    vj
    @196
    @203
    @215
    @190
    esumgsum
    3brtr3d
    eqbrtrd
    adantlr
    adantlr
    xrltletrd
    rspcedvd
    adantllr
    syl21anc
    @153
    @156
    vc
    @15
    wrex
    #
    @149
    @151
    @153
    @216
    vc
    @15
    @18
    @150
    @19
    @88
    @101
    elrnmpti
    biimpi
    ad2antlr
    r19.29af
    @149
    @31
    @151
    vu
    @20
    wrex
    wph
    @148
    @31
    wph
    vr
    vs
    vt
    cxr
    @20
    @24
    clt
    @23
    @116
    suplub
    imp
    @30
    @151
    vt
    vu
    @20
    @29
    @150
    @24
    clt
    breq2
    cbvrexv
    sylib
    r19.29a
    eqsupd
    wph
    va
    cA
    @5
    @7
    vj
    cV
    @75
    vj
    cA
    nfcv
    esum2d.2
    @142
    @127
    @7
    eqidd
    esumval
    @144
    3eqtr4d
end
