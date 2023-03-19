include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmin.mm"
include "co.mm"
include "cn.mm"
include "cfv.mm"
include "cif.mm"
include "cico.mm"
include "cvol.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cicc.mm"
include "crab.mm"
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "cxr.mm"
include "rexrd.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "cc0.mm"
include "recnd.mm"
include "subidd.mm"
include "cvv.mm"
include "nfv.mm"
include "nnex.mm"
include "cdm.mm"
include "cpnf.mm"
include "wf.mm"
include "volf.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "ifcld.mm"
include "icombl.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "sge0ge0mpt.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2.mm"
include "id.mm"
include "ifbieq2d.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "mpteq2dv.mm"
include "breq12d.mm"
include "elrab.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "syl.mm"
include "supicc.mm"
include "syl5eqel.mm"
include "caddc.mm"
include "iccssred.mm"
include "sstrd.mm"
include "sselda.mm"
include "wn.mm"
include "adantlr.mm"
include "sge0xrclmpt.mm"
include "pnfxr.mm"
include "leidd.mm"
include "min1.mm"
include "icossico.mm"
include "syl22anc.mm"
include "volss.mm"
include "sge0lempt.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "xrltned.mm"
include "neneqd.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "readdcld.mm"
include "sseldd.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "lesubaddd.mm"
include "mpbid.mm"
include "eqidd.mm"
include "iftrue.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "w3a.mm"
include "iccsupr.mm"
include "simp3d.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "ad2antrr.mm"
include "letrd.mm"
include "iftrued.mm"
include "3eqtr4d.mm"
include "eqled.mm"
include "ltnled.mm"
include "iffalse.mm"
include "ad2antlr.mm"
include "pm2.61dan.mm"
include "leadd1dd.mm"
include "ex.mm"
include "ralrimi.mm"
include "wb.mm"
include "suprleub.mm"
include "3jca.mm"

theorem hoidmv1lelem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  assume hoidmv1lelem1.a: |- ( ph -> A e. RR )
  assume hoidmv1lelem1.b: |- ( ph -> B e. RR )
  assume hoidmv1lelem1.l: |- ( ph -> A < B )
  assume hoidmv1lelem1.c: |- ( ph -> C : NN --> RR )
  assume hoidmv1lelem1.d: |- ( ph -> D : NN --> RR )
  assume hoidmv1lelem1.r: |- ( ph -> ( sum^ ` ( j e. NN |-> ( vol ` ( ( C ` j ) [,) ( D ` j ) ) ) ) ) e. RR )
  assume hoidmv1lelem1.u: |- U = { z e. ( A [,] B ) | ( z - A ) <_ ( sum^ ` ( j e. NN |-> ( vol ` ( ( C ` j ) [,) if ( ( D ` j ) <_ z , ( D ` j ) , z ) ) ) ) ) }
  assume hoidmv1lelem1.s: |- S = sup ( U , RR , < )

  disjoint A j
  disjoint A z
  disjoint j z
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint S j
  disjoint S z
  disjoint U j
  disjoint U z
  disjoint U x
  disjoint U y
  disjoint j ph
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( S e. U /\ A e. U /\ E. x e. RR A. y e. U y <_ x ) )

  proof
    wph
    cS
    cU
    wcel
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
    cS
    vz
    cv
    #
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
    @4
    cD
    cfv
    #
    @2
    cle
    wbr
    #
    @6
    @2
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
    cA
    cB
    cicc
    co
    #
    crab
    #
    cU
    wph
    cS
    @14
    wcel
    #
    cS
    cA
    cmin
    co
    #
    vj
    cn
    @5
    @6
    cS
    cle
    wbr
    #
    @6
    cS
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
    wa
    cS
    @15
    wcel
    wph
    @16
    @24
    wph
    cS
    cU
    cr
    clt
    csup
    #
    @14
    hoidmv1lelem1.s
    wph
    cU
    cA
    cB
    hoidmv1lelem1.a
    hoidmv1lelem1.b
    cU
    @14
    wss
    #
    wph
    cU
    @15
    @14
    hoidmv1lelem1.u
    @13
    vz
    @14
    ssrab2
    eqsstri
    a1i
    #
    wph
    @0
    cU
    c0
    wne
    #
    wph
    cA
    @15
    cU
    wph
    cA
    @14
    wcel
    #
    cA
    cA
    cmin
    co
    #
    vj
    cn
    @5
    @6
    cA
    cle
    wbr
    #
    @6
    cA
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
    wa
    cA
    @15
    wcel
    wph
    @29
    @37
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    @29
    wph
    cA
    hoidmv1lelem1.a
    rexrd
    wph
    cB
    hoidmv1lelem1.b
    rexrd
    wph
    cA
    cB
    hoidmv1lelem1.a
    hoidmv1lelem1.b
    hoidmv1lelem1.l
    ltled
    cA
    cB
    lbicc2
    syl3anc
    wph
    @30
    cc0
    @36
    cle
    wph
    cA
    wph
    cA
    hoidmv1lelem1.a
    recnd
    subidd
    wph
    cn
    @34
    vj
    cvv
    wph
    vj
    nfv
    #
    cn
    cvv
    wcel
    #
    wph
    nnex
    a1i
    #
    wph
    @4
    cn
    wcel
    #
    wa
    #
    cvol
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    @33
    cvol
    @43
    @44
    cvol
    wf
    #
    @42
    volf
    a1i
    #
    @42
    @5
    cr
    wcel
    #
    @32
    cxr
    wcel
    @33
    @43
    wcel
    wph
    cn
    cr
    @4
    cC
    hoidmv1lelem1.c
    ffvelrnda
    #
    @42
    @32
    @42
    @31
    @6
    cA
    cr
    wph
    cn
    cr
    @4
    cD
    hoidmv1lelem1.d
    ffvelrnda
    #
    wph
    cA
    cr
    wcel
    #
    @41
    hoidmv1lelem1.a
    adantr
    ifcld
    rexrd
    @5
    @32
    icombl
    syl2anc
    ffvelrnd
    sge0ge0mpt
    eqbrtrd
    jca
    @13
    @37
    vz
    cA
    @14
    @2
    cA
    wceq
    #
    @3
    @30
    @12
    @36
    cle
    @2
    cA
    cA
    cmin
    oveq1
    @51
    @11
    @35
    csumge0
    @51
    vj
    cn
    @10
    @34
    @51
    @9
    @33
    cvol
    @51
    @8
    @32
    @5
    cico
    @51
    @7
    @31
    @2
    cA
    @6
    @2
    cA
    @6
    cle
    breq2
    @51
    id
    ifbieq2d
    oveq2d
    fveq2d
    mpteq2dv
    fveq2d
    breq12d
    elrab
    sylibr
    hoidmv1lelem1.u
    syl6eleqr
    #
    cU
    cA
    ne0i
    syl
    #
    supicc
    syl5eqel
    #
    wph
    @24
    cS
    @23
    cA
    caddc
    co
    #
    cle
    wbr
    wph
    cS
    @25
    @55
    cle
    cS
    @25
    wceq
    wph
    hoidmv1lelem1.s
    a1i
    wph
    @25
    @55
    cle
    wbr
    #
    @2
    @55
    cle
    wbr
    #
    vz
    cU
    wral
    #
    wph
    @57
    vz
    cU
    wph
    vz
    nfv
    wph
    @2
    cU
    wcel
    #
    @57
    wph
    @59
    wa
    #
    @2
    @12
    cA
    caddc
    co
    #
    @55
    wph
    cU
    cr
    @2
    wph
    cU
    @14
    cr
    @27
    wph
    cA
    cB
    hoidmv1lelem1.a
    hoidmv1lelem1.b
    iccssred
    #
    sstrd
    #
    sselda
    #
    @60
    @12
    cA
    @60
    @12
    cr
    wcel
    @12
    cpnf
    wceq
    wn
    @60
    @12
    cpnf
    @60
    @12
    cpnf
    @60
    vj
    cn
    @10
    cvv
    @60
    vj
    nfv
    #
    @39
    @60
    nnex
    a1i
    #
    @60
    @41
    wa
    #
    @43
    @44
    @9
    cvol
    @45
    @67
    volf
    a1i
    @67
    @47
    @8
    cxr
    wcel
    @9
    @43
    wcel
    #
    wph
    @41
    @47
    @59
    @48
    adantlr
    @67
    @8
    @67
    @7
    @6
    @2
    cr
    wph
    @41
    @6
    cr
    wcel
    #
    @59
    @49
    adantlr
    #
    @60
    @2
    cr
    wcel
    #
    @41
    @64
    adantr
    #
    ifcld
    #
    rexrd
    @5
    @8
    icombl
    syl2anc
    #
    ffvelrnd
    #
    sge0xrclmpt
    #
    cpnf
    cxr
    wcel
    #
    @60
    pnfxr
    a1i
    #
    @60
    @12
    vj
    cn
    @5
    @6
    cico
    co
    #
    cvol
    cfv
    #
    cmpt
    csumge0
    cfv
    #
    cpnf
    @76
    wph
    @81
    cxr
    wcel
    @59
    wph
    @81
    hoidmv1lelem1.r
    rexrd
    #
    adantr
    @78
    @60
    vj
    cn
    @10
    @80
    cvv
    @65
    @66
    @75
    wph
    @41
    @80
    @44
    wcel
    @59
    @42
    @43
    @44
    @79
    cvol
    @46
    @42
    @47
    @6
    cxr
    wcel
    #
    @79
    @43
    wcel
    #
    @48
    @42
    @6
    @49
    rexrd
    #
    @5
    @6
    icombl
    syl2anc
    #
    ffvelrnd
    #
    adantlr
    @67
    @68
    @84
    @9
    @79
    wss
    #
    @10
    @80
    cle
    wbr
    @74
    wph
    @41
    @84
    @59
    @86
    adantlr
    @67
    @5
    cxr
    wcel
    #
    @83
    @5
    @5
    cle
    wbr
    #
    @8
    @6
    cle
    wbr
    #
    @88
    wph
    @41
    @89
    @59
    @42
    @5
    @48
    rexrd
    #
    adantlr
    #
    wph
    @41
    @83
    @59
    @85
    adantlr
    wph
    @41
    @90
    @59
    @42
    @5
    @48
    leidd
    #
    adantlr
    #
    @67
    @69
    @71
    @91
    @70
    @72
    @6
    @2
    min1
    syl2anc
    @5
    @6
    @5
    @8
    icossico
    syl22anc
    @9
    @79
    volss
    syl3anc
    sge0lempt
    wph
    @81
    cpnf
    clt
    wbr
    @59
    wph
    @81
    hoidmv1lelem1.r
    ltpnfd
    #
    adantr
    xrlelttrd
    xrltned
    neneqd
    @60
    @11
    cvv
    cn
    @66
    @60
    vj
    cn
    @10
    @44
    @11
    @75
    @11
    eqid
    fmptd
    sge0repnf
    mpbird
    #
    wph
    @50
    @59
    hoidmv1lelem1.a
    adantr
    #
    readdcld
    wph
    @55
    cr
    wcel
    #
    @59
    wph
    @23
    cA
    wph
    @23
    cr
    wcel
    #
    @23
    cpnf
    wceq
    wn
    wph
    @23
    cpnf
    wph
    @23
    cpnf
    wph
    vj
    cn
    @21
    cvv
    @38
    @40
    @42
    @43
    @44
    @20
    cvol
    @46
    @42
    @47
    @19
    cxr
    wcel
    #
    @20
    @43
    wcel
    #
    @48
    @42
    @19
    @42
    @18
    @6
    cS
    cr
    @49
    wph
    cS
    cr
    wcel
    #
    @41
    wph
    @14
    cr
    cS
    @62
    @54
    sseldd
    #
    adantr
    #
    ifcld
    rexrd
    #
    @5
    @19
    icombl
    syl2anc
    #
    ffvelrnd
    #
    sge0xrclmpt
    #
    @77
    wph
    pnfxr
    a1i
    #
    wph
    @23
    @81
    cpnf
    @109
    @82
    @110
    wph
    vj
    cn
    @21
    @80
    cvv
    @38
    @40
    @108
    @87
    @42
    @102
    @84
    @20
    @79
    wss
    #
    @21
    @80
    cle
    wbr
    @107
    @86
    @42
    @89
    @83
    @90
    @19
    @6
    cle
    wbr
    #
    @111
    @92
    @85
    @94
    @42
    @69
    @103
    @112
    @49
    @105
    @6
    cS
    min1
    syl2anc
    @5
    @6
    @5
    @19
    icossico
    syl22anc
    @20
    @79
    volss
    syl3anc
    sge0lempt
    @96
    xrlelttrd
    xrltned
    neneqd
    wph
    @22
    cvv
    cn
    @40
    wph
    vj
    cn
    @21
    @44
    @22
    @108
    @22
    eqid
    fmptd
    sge0repnf
    mpbird
    #
    hoidmv1lelem1.a
    readdcld
    #
    adantr
    @60
    @13
    @2
    @61
    cle
    wbr
    @60
    @2
    @14
    wcel
    #
    @13
    @60
    @2
    @15
    wcel
    #
    @115
    @13
    wa
    @59
    @116
    wph
    @59
    @116
    cU
    @15
    @2
    hoidmv1lelem1.u
    eleq2i
    #
    biimpi
    adantl
    #
    @13
    vz
    @14
    rabid
    sylib
    simprd
    @60
    @2
    cA
    @12
    @64
    @98
    @97
    lesubaddd
    mpbid
    @60
    @12
    @23
    cA
    @97
    wph
    @100
    @59
    @113
    adantr
    @98
    @60
    vj
    cn
    @10
    @21
    cvv
    @65
    @66
    @75
    wph
    @41
    @21
    @44
    wcel
    @59
    @108
    adantlr
    @67
    @68
    @102
    @9
    @20
    wss
    #
    @10
    @21
    cle
    wbr
    @74
    wph
    @41
    @102
    @59
    @107
    adantlr
    @67
    @89
    @101
    @90
    @8
    @19
    cle
    wbr
    #
    @119
    @93
    wph
    @41
    @101
    @59
    @106
    adantlr
    @95
    @67
    @7
    @120
    @67
    @7
    wa
    #
    @8
    @19
    @67
    @8
    cr
    wcel
    @7
    @73
    adantr
    @121
    @6
    @6
    @8
    @19
    @121
    @6
    eqidd
    @7
    @8
    @6
    wceq
    @67
    @7
    @6
    @2
    iftrue
    adantl
    @121
    @18
    @6
    cS
    @121
    @6
    @2
    cS
    @67
    @69
    @7
    @70
    adantr
    @67
    @71
    @7
    @72
    adantr
    wph
    @103
    @59
    @41
    @7
    @104
    ad3antrrr
    @67
    @7
    simpr
    @60
    @2
    cS
    cle
    wbr
    #
    @41
    @7
    @60
    @2
    @25
    cS
    cle
    @60
    cU
    cr
    wss
    #
    @28
    @1
    @59
    @2
    @25
    cle
    wbr
    wph
    @123
    @59
    @63
    adantr
    wph
    @28
    @59
    @53
    adantr
    wph
    @1
    @59
    wph
    @123
    @28
    @1
    wph
    @50
    cB
    cr
    wcel
    #
    wa
    @26
    @0
    @123
    @28
    @1
    w3a
    wph
    @50
    @124
    hoidmv1lelem1.a
    hoidmv1lelem1.b
    jca
    @27
    @52
    vx
    vy
    cA
    cB
    cA
    cU
    iccsupr
    syl3anc
    simp3d
    #
    adantr
    @60
    @116
    @59
    @118
    @117
    sylibr
    vx
    vy
    cU
    @2
    suprub
    syl31anc
    hoidmv1lelem1.s
    syl6breqr
    #
    ad2antrr
    letrd
    iftrued
    3eqtr4d
    eqled
    @67
    @7
    wn
    #
    wa
    #
    @18
    @120
    @128
    @18
    wa
    #
    @120
    @2
    @6
    cle
    wbr
    #
    @128
    @130
    @18
    @128
    @2
    @6
    @67
    @71
    @127
    @72
    adantr
    #
    @67
    @69
    @127
    @70
    adantr
    #
    @128
    @2
    @6
    clt
    wbr
    @127
    @67
    @127
    simpr
    @128
    @2
    @6
    @131
    @132
    ltnled
    mpbird
    ltled
    adantr
    @129
    @8
    @2
    @19
    @6
    cle
    @127
    @8
    @2
    wceq
    #
    @67
    @18
    @7
    @6
    @2
    iffalse
    #
    ad2antlr
    @18
    @19
    @6
    wceq
    @128
    @18
    @6
    cS
    iftrue
    adantl
    breq12d
    mpbird
    @128
    @18
    wn
    #
    wa
    #
    @120
    @122
    @60
    @122
    @41
    @127
    @135
    @126
    ad3antrrr
    @136
    @8
    @2
    @19
    cS
    cle
    @127
    @133
    @67
    @135
    @134
    ad2antlr
    @135
    @19
    cS
    wceq
    @128
    @18
    @6
    cS
    iffalse
    adantl
    breq12d
    mpbird
    pm2.61dan
    pm2.61dan
    @5
    @19
    @5
    @8
    icossico
    syl22anc
    @9
    @20
    volss
    syl3anc
    sge0lempt
    leadd1dd
    letrd
    ex
    ralrimi
    wph
    @123
    @28
    @1
    @99
    @56
    @58
    wb
    @63
    @53
    @125
    @114
    vx
    vy
    vz
    cU
    @55
    suprleub
    syl31anc
    mpbird
    eqbrtrd
    wph
    cS
    cA
    @23
    @104
    hoidmv1lelem1.a
    @113
    lesubaddd
    mpbird
    jca
    @13
    @24
    vz
    cS
    @14
    @2
    cS
    wceq
    #
    @3
    @17
    @12
    @23
    cle
    @2
    cS
    cA
    cmin
    oveq1
    @137
    @11
    @22
    csumge0
    @137
    vj
    cn
    @10
    @21
    @137
    @9
    @20
    cvol
    @137
    @8
    @19
    @5
    cico
    @137
    @7
    @18
    @2
    cS
    @6
    @2
    cS
    @6
    cle
    breq2
    @137
    id
    ifbieq2d
    oveq2d
    fveq2d
    mpteq2dv
    fveq2d
    breq12d
    elrab
    sylibr
    hoidmv1lelem1.u
    syl6eleqr
    @52
    @125
    3jca
end
