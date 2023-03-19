include "cmin.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cico.mm"
include "cvol.mm"
include "cmpt.mm"
include "csumge0.mm"
include "resubcld.mm"
include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "wn.mm"
include "cvv.mm"
include "nnex.mm"
include "a1i.mm"
include "cc0.mm"
include "cicc.mm"
include "wa.mm"
include "icossicc.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "ifcld.mm"
include "volicore.mm"
include "syl2anc.mm"
include "rexrd.mm"
include "cdm.mm"
include "icombl.mm"
include "volge0.mm"
include "syl.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "sseldi.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0xrcl.mm"
include "nfv.mm"
include "wf.mm"
include "volf.mm"
include "ffvelrnd.mm"
include "wss.mm"
include "leidd.mm"
include "min1.mm"
include "icossico.mm"
include "syl22anc.mm"
include "volss.mm"
include "syl3anc.mm"
include "sge0lempt.mm"
include "xrlelttrd.mm"
include "xrltned.mm"
include "neneqd.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "crab.mm"
include "iccssred.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "wral.mm"
include "wrex.mm"
include "hoidmv1lelem1.mm"
include "simp1d.mm"
include "sseldd.mm"
include "clt.mm"
include "simpl.mm"
include "simpr.mm"
include "ltnled.mm"
include "ciun.mm"
include "csup.mm"
include "c0.mm"
include "wne.mm"
include "syl5ss.mm"
include "ne0i.mm"
include "simp3d.mm"
include "simp2d.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "eliun.mm"
include "sylib.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "fveq2i.mm"
include "syl5eqel.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "eqcomi.mm"
include "breq2i.mm"
include "rabbii.mm"
include "eqtri.mm"
include "simp2.mm"
include "simp3.mm"
include "hoidmv1lelem2.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "jca.mm"
include "iccsupr.mm"
include "ralrimiva.mm"
include "sseli.mm"
include "adantl.mm"
include "lenltd.mm"
include "ralbidva.mm"
include "mpbid.mm"
include "ralnex.mm"
include "condan.mm"
include "iccleub.mm"
include "xrletrid.mm"
include "eqeltrd.mm"
include "syl6eleq.mm"
include "oveq1.mm"
include "breq2.mm"
include "id.mm"
include "ifbieq2d.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "elrab.mm"
include "simprd.mm"
include "letrd.mm"

theorem hoidmv1lelem3
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let vj: setvar j
  let vy: setvar y
  let vi: setvar i
  let vu: setvar u
  let vx: setvar x
  let vk: setvar k
  assume hoidmv1lelem3.a: |- ( ph -> A e. RR )
  assume hoidmv1lelem3.b: |- ( ph -> B e. RR )
  assume hoidmv1lelem3.l: |- ( ph -> A < B )
  assume hoidmv1lelem3.c: |- ( ph -> C : NN --> RR )
  assume hoidmv1lelem3.d: |- ( ph -> D : NN --> RR )
  assume hoidmv1lelem3.x: |- ( ph -> ( A [,) B ) C_ U_ j e. NN ( ( C ` j ) [,) ( D ` j ) ) )
  assume hoidmv1lelem3.r: |- ( ph -> ( sum^ ` ( j e. NN |-> ( vol ` ( ( C ` j ) [,) ( D ` j ) ) ) ) ) e. RR )
  assume hoidmv1lelem3.u: |- U = { z e. ( A [,] B ) | ( z - A ) <_ ( sum^ ` ( j e. NN |-> ( vol ` ( ( C ` j ) [,) if ( ( D ` j ) <_ z , ( D ` j ) , z ) ) ) ) ) }
  assume hoidmv1lelem3.s: |- S = sup ( U , RR , < )

  disjoint A j
  disjoint A z
  disjoint j z
  disjoint B j
  disjoint B z
  disjoint C j
  disjoint C z
  disjoint D j
  disjoint D z
  disjoint S j
  disjoint S z
  disjoint U j
  disjoint U z
  disjoint j ph
  disjoint ph z
  disjoint A y
  disjoint B i
  disjoint i j
  disjoint i z
  disjoint B u
  disjoint j u
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C i
  disjoint D i
  disjoint D u
  disjoint S i
  disjoint S u
  disjoint U u
  disjoint U x
  disjoint U y
  disjoint i ph
  disjoint ph u
  disjoint k x
  assert |- ( ph -> ( B - A ) <_ ( sum^ ` ( j e. NN |-> ( vol ` ( ( C ` j ) [,) ( D ` j ) ) ) ) ) )

  proof
    wph
    cB
    cA
    cmin
    co
    #
    vj
    cn
    vj
    cv
    #
    cC
    cfv
    #
    @1
    cD
    cfv
    #
    cB
    cle
    wbr
    #
    @3
    cB
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    vj
    cn
    @2
    @3
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    wph
    cB
    cA
    hoidmv1lelem3.b
    hoidmv1lelem3.a
    resubcld
    wph
    @9
    cr
    wcel
    @9
    cpnf
    wceq
    wn
    wph
    @9
    cpnf
    wph
    @9
    cpnf
    wph
    @8
    cvv
    cn
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    wph
    vj
    cn
    @7
    cc0
    cpnf
    cicc
    co
    #
    @8
    wph
    @1
    cn
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    @15
    @7
    cc0
    cpnf
    icossicc
    @17
    cc0
    cpnf
    @7
    cc0
    cxr
    wcel
    @17
    0xr
    a1i
    cpnf
    cxr
    wcel
    #
    @17
    pnfxr
    a1i
    @17
    @7
    @17
    @2
    cr
    wcel
    #
    @5
    cr
    wcel
    @7
    cr
    wcel
    wph
    cn
    cr
    @1
    cC
    hoidmv1lelem3.c
    ffvelrnda
    #
    @17
    @4
    @3
    cB
    cr
    wph
    cn
    cr
    @1
    cD
    hoidmv1lelem3.d
    ffvelrnda
    #
    wph
    cB
    cr
    wcel
    #
    @16
    hoidmv1lelem3.b
    adantr
    #
    ifcld
    #
    @2
    @5
    volicore
    syl2anc
    #
    rexrd
    @17
    @6
    cvol
    cdm
    #
    wcel
    #
    cc0
    @7
    cle
    wbr
    @17
    @19
    @5
    cxr
    wcel
    @27
    @20
    @17
    @5
    @24
    rexrd
    @2
    @5
    icombl
    syl2anc
    #
    @6
    volge0
    syl
    @17
    @7
    @25
    ltpnfd
    elicod
    sseldi
    #
    @8
    eqid
    fmptd
    #
    sge0xrcl
    #
    @18
    wph
    pnfxr
    a1i
    #
    wph
    @9
    @13
    cpnf
    @31
    wph
    @13
    hoidmv1lelem3.r
    rexrd
    @32
    wph
    vj
    cn
    @7
    @11
    cvv
    wph
    vj
    nfv
    @14
    @29
    @17
    @26
    @15
    @10
    cvol
    @26
    @15
    cvol
    wf
    @17
    volf
    a1i
    @17
    @19
    @3
    cxr
    wcel
    #
    @10
    @26
    wcel
    #
    @20
    @17
    @3
    @21
    rexrd
    #
    @2
    @3
    icombl
    syl2anc
    #
    ffvelrnd
    @17
    @27
    @34
    @6
    @10
    wss
    #
    @7
    @11
    cle
    wbr
    @28
    @36
    @17
    @2
    cxr
    wcel
    @33
    @2
    @2
    cle
    wbr
    @5
    @3
    cle
    wbr
    #
    @37
    @17
    @2
    @20
    rexrd
    @35
    @17
    @2
    @20
    leidd
    @17
    @3
    cr
    wcel
    @22
    @38
    @21
    @23
    @3
    cB
    min1
    syl2anc
    @2
    @3
    @2
    @5
    icossico
    syl22anc
    @6
    @10
    volss
    syl3anc
    sge0lempt
    #
    wph
    @13
    hoidmv1lelem3.r
    ltpnfd
    xrlelttrd
    xrltned
    neneqd
    wph
    @8
    cvv
    cn
    @14
    @30
    sge0repnf
    mpbird
    hoidmv1lelem3.r
    wph
    cB
    cA
    cB
    cicc
    co
    #
    wcel
    #
    @0
    @9
    cle
    wbr
    #
    wph
    cB
    vz
    cv
    #
    cA
    cmin
    co
    #
    vj
    cn
    @2
    @3
    @43
    cle
    wbr
    #
    @3
    @43
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    vz
    @40
    crab
    #
    wcel
    @41
    @42
    wa
    wph
    cB
    cU
    @52
    wph
    cB
    cS
    cU
    wph
    cB
    cS
    wph
    cB
    hoidmv1lelem3.b
    rexrd
    #
    wph
    cS
    wph
    @40
    cr
    cS
    wph
    cA
    cB
    hoidmv1lelem3.a
    hoidmv1lelem3.b
    iccssred
    #
    wph
    cU
    @40
    cS
    cU
    @52
    @40
    hoidmv1lelem3.u
    @51
    vz
    @40
    ssrab2
    eqsstri
    #
    wph
    cS
    cU
    wcel
    #
    cA
    cU
    wcel
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cU
    wral
    vx
    cr
    wrex
    #
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cS
    cU
    vj
    hoidmv1lelem3.a
    hoidmv1lelem3.b
    hoidmv1lelem3.l
    hoidmv1lelem3.c
    hoidmv1lelem3.d
    hoidmv1lelem3.r
    hoidmv1lelem3.u
    hoidmv1lelem3.s
    hoidmv1lelem1
    #
    simp1d
    #
    sseldi
    #
    sseldd
    #
    rexrd
    #
    wph
    cB
    cS
    cle
    wbr
    #
    cS
    vu
    cv
    #
    clt
    wbr
    #
    vu
    cU
    wrex
    #
    wph
    @64
    wn
    #
    wa
    #
    wph
    cS
    cB
    clt
    wbr
    #
    @67
    wph
    @68
    simpl
    #
    @69
    @70
    @68
    wph
    @68
    simpr
    @69
    cS
    cB
    @69
    wph
    cS
    cr
    wcel
    #
    @71
    @62
    syl
    @69
    wph
    @22
    @71
    hoidmv1lelem3.b
    syl
    ltnled
    mpbird
    wph
    @70
    wa
    #
    cS
    @10
    wcel
    #
    vj
    cn
    wrex
    #
    @67
    @73
    cS
    vj
    cn
    @10
    ciun
    #
    wcel
    @75
    @73
    cA
    cB
    cico
    co
    #
    @76
    cS
    wph
    @77
    @76
    wss
    @70
    hoidmv1lelem3.x
    adantr
    @73
    cA
    cB
    cS
    wph
    cA
    cxr
    wcel
    #
    @70
    wph
    cA
    hoidmv1lelem3.a
    rexrd
    #
    adantr
    wph
    cB
    cxr
    wcel
    #
    @70
    @53
    adantr
    wph
    cS
    cxr
    wcel
    @70
    @63
    adantr
    wph
    cA
    cS
    cle
    wbr
    #
    @70
    wph
    cA
    cU
    cr
    clt
    csup
    #
    cS
    cle
    wph
    cU
    cr
    wss
    #
    cU
    c0
    wne
    #
    @58
    @57
    cA
    @82
    cle
    wbr
    wph
    cU
    @40
    cr
    @55
    @54
    syl5ss
    wph
    @56
    @84
    @60
    cU
    cS
    ne0i
    syl
    #
    wph
    @56
    @57
    @58
    @59
    simp3d
    wph
    @56
    @57
    @58
    @59
    simp2d
    vx
    vy
    cU
    cA
    suprub
    syl31anc
    hoidmv1lelem3.s
    syl6breqr
    adantr
    #
    wph
    @70
    simpr
    #
    elicod
    sseldd
    vj
    cS
    cn
    @10
    eliun
    sylib
    @73
    @74
    @67
    vj
    cn
    @73
    @16
    @74
    @67
    @73
    @16
    @74
    w3a
    vz
    vu
    cA
    cB
    cC
    cD
    cS
    cU
    vi
    @1
    @5
    @73
    @16
    cA
    cr
    wcel
    #
    @74
    wph
    @88
    @70
    hoidmv1lelem3.a
    adantr
    3ad2ant1
    @73
    @16
    @22
    @74
    wph
    @22
    @70
    hoidmv1lelem3.b
    adantr
    3ad2ant1
    @73
    @16
    cn
    cr
    cC
    wf
    #
    @74
    wph
    @89
    @70
    hoidmv1lelem3.c
    adantr
    3ad2ant1
    @73
    @16
    cn
    cr
    cD
    wf
    #
    @74
    wph
    @90
    @70
    hoidmv1lelem3.d
    adantr
    3ad2ant1
    @73
    @16
    vi
    cn
    vi
    cv
    #
    cC
    cfv
    #
    @91
    cD
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cr
    wcel
    #
    @74
    wph
    @98
    @70
    wph
    @97
    @13
    cr
    @96
    @12
    csumge0
    vi
    vj
    cn
    @95
    @11
    @91
    @1
    wceq
    #
    @94
    @10
    cvol
    @99
    @92
    @2
    @93
    @3
    cico
    @91
    @1
    cC
    fveq2
    #
    @91
    @1
    cD
    fveq2
    #
    oveq12d
    fveq2d
    cbvmptv
    fveq2i
    hoidmv1lelem3.r
    syl5eqel
    adantr
    3ad2ant1
    cU
    @52
    @44
    vi
    cn
    @92
    @93
    @43
    cle
    wbr
    #
    @93
    @43
    cif
    #
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    vz
    @40
    crab
    hoidmv1lelem3.u
    @51
    @108
    vz
    @40
    @50
    @107
    @44
    cle
    @49
    @106
    csumge0
    @106
    @49
    vi
    vj
    cn
    @105
    @48
    @99
    @104
    @47
    cvol
    @99
    @92
    @2
    @103
    @46
    cico
    @100
    @99
    @102
    @45
    @93
    @3
    @43
    @99
    @93
    @3
    @43
    cle
    @101
    breq1d
    @101
    ifbieq1d
    oveq12d
    fveq2d
    cbvmptv
    eqcomi
    fveq2i
    breq2i
    rabbii
    eqtri
    @73
    @16
    @56
    @74
    wph
    @56
    @70
    @60
    adantr
    3ad2ant1
    @73
    @16
    @81
    @74
    @86
    3ad2ant1
    @73
    @16
    @70
    @74
    @87
    3ad2ant1
    @73
    @16
    @74
    simp2
    @73
    @16
    @74
    simp3
    @5
    eqid
    hoidmv1lelem2
    3exp
    rexlimdv
    mpd
    syl2anc
    wph
    @67
    wn
    #
    @68
    wph
    @66
    wn
    #
    vu
    cU
    wral
    #
    @109
    wph
    @65
    cS
    cle
    wbr
    #
    vu
    cU
    wral
    @111
    wph
    @112
    vu
    cU
    wph
    @65
    cU
    wcel
    #
    wa
    #
    @65
    @82
    cS
    cle
    @114
    @83
    @84
    @58
    @113
    @65
    @82
    cle
    wbr
    @114
    cU
    @40
    cr
    @55
    wph
    @40
    cr
    wss
    @113
    @54
    adantr
    #
    syl5ss
    wph
    @84
    @113
    @85
    adantr
    @114
    @83
    @84
    @58
    @114
    @88
    @22
    wa
    #
    cU
    @40
    wss
    #
    @56
    @83
    @84
    @58
    w3a
    wph
    @116
    @113
    wph
    @88
    @22
    hoidmv1lelem3.a
    hoidmv1lelem3.b
    jca
    adantr
    @117
    @114
    @55
    a1i
    wph
    @56
    @113
    @60
    adantr
    vx
    vy
    cA
    cB
    cS
    cU
    iccsupr
    syl3anc
    simp3d
    wph
    @113
    simpr
    vx
    vy
    cU
    @65
    suprub
    syl31anc
    hoidmv1lelem3.s
    syl6breqr
    ralrimiva
    wph
    @112
    @110
    vu
    cU
    @114
    @65
    cS
    @114
    @40
    cr
    @65
    @115
    @113
    @65
    @40
    wcel
    wph
    cU
    @40
    @65
    @55
    sseli
    adantl
    sseldd
    wph
    @72
    @113
    @62
    adantr
    lenltd
    ralbidva
    mpbid
    @66
    vu
    cU
    ralnex
    sylib
    adantr
    condan
    wph
    @78
    @80
    cS
    @40
    wcel
    cS
    cB
    cle
    wbr
    @79
    @53
    @61
    cA
    cB
    cS
    iccleub
    syl3anc
    xrletrid
    @60
    eqeltrd
    hoidmv1lelem3.u
    syl6eleq
    @51
    @42
    vz
    cB
    @40
    @43
    cB
    wceq
    #
    @44
    @0
    @50
    @9
    cle
    @43
    cB
    cA
    cmin
    oveq1
    @118
    @49
    @8
    csumge0
    @118
    vj
    cn
    @48
    @7
    @118
    @47
    @6
    cvol
    @118
    @46
    @5
    @2
    cico
    @118
    @45
    @4
    @43
    cB
    @3
    @43
    cB
    @3
    cle
    breq2
    @118
    id
    ifbieq2d
    oveq2d
    fveq2d
    mpteq2dv
    fveq2d
    breq12d
    elrab
    sylib
    simprd
    @39
    letrd
end
