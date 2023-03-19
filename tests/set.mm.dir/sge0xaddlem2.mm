include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cxad.mm"
include "nfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cico.mm"
include "cr.mm"
include "rge0ssre.mm"
include "sseldi.mm"
include "readdcld.mm"
include "rexrd.mm"
include "cicc.mm"
include "cle.mm"
include "wbr.mm"
include "icossicc.mm"
include "xrge0ge0.mm"
include "syl.mm"
include "addge0d.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "sge0revalmpt.mm"
include "wceq.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eqcomd.mm"
include "eqeltrd.mm"
include "eqeltrrd.mm"
include "wss.mm"
include "wral.mm"
include "elinel2.mm"
include "adantl.mm"
include "simpll.mm"
include "elpwinss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantll.mm"
include "fsumrecl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "supxrcl.mm"
include "crp.mm"
include "c2.mm"
include "cdiv.mm"
include "wrex.mm"
include "adantlr.mm"
include "rphalfcl.mm"
include "sge0ltfirpmpt2.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "csb.mm"
include "simpl1l.mm"
include "3ad2antl1.mm"
include "wi.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "simp11r.mm"
include "simp12.mm"
include "3ad2ant2.mm"
include "simp2.mm"
include "simp13.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "fveq2i.mm"
include "cbvsum.mm"
include "oveq1i.mm"
include "breq12i.mm"
include "biimpi.mm"
include "simp3.mm"
include "simp11l.mm"
include "nfov.mm"
include "mpteq2i.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "eqcomi.mm"
include "eqtr4d.mm"
include "ge0xaddcl.mm"
include "sge0clmpt.mm"
include "syl5eqelr.mm"
include "sge0xaddlem1.mm"
include "oveq12i.mm"
include "sylibr.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "eqbrtrd.mm"
include "xrlexaddrp.mm"
include "sge0fsummpt.mm"
include "recnd.mm"
include "fsumadd.mm"
include "eqtrd.mm"
include "cvv.mm"
include "eqidd.mm"
include "sumeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "elexd.mm"
include "elrnmptd.mm"
include "supxrub.mm"
include "rnmptssd.mm"
include "le2addd.mm"
include "sge0lefimpt.mm"
include "mpbird.mm"
include "xrletrid.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"

theorem sge0xaddlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let ve: setvar e
  let vj: setvar j
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sge0xaddlem2.a: |- ( ph -> A e. V )
  assume sge0xaddlem2.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )
  assume sge0xaddlem2.c: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,) +oo ) )
  assume sge0xaddlem2.sb: |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) e. RR )
  assume sge0xaddlem2.sc: |- ( ph -> ( sum^ ` ( k e. A |-> C ) ) e. RR )

  disjoint A k
  disjoint k ph
  disjoint A e
  disjoint A j
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint e j
  disjoint e k
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint A y
  disjoint e y
  disjoint k y
  disjoint x y
  disjoint A z
  disjoint e z
  disjoint k z
  disjoint x z
  disjoint B e
  disjoint B j
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint C e
  disjoint C j
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint C z
  disjoint e ph
  disjoint j ph
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> ( B +e C ) ) ) = ( ( sum^ ` ( k e. A |-> B ) ) +e ( sum^ ` ( k e. A |-> C ) ) ) )

  proof
    wph
    vk
    cA
    cB
    cC
    caddc
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    @0
    vk
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    vk
    cA
    cB
    cC
    cxad
    co
    #
    cmpt
    #
    csumge0
    cfv
    vk
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    #
    vk
    cA
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cxad
    co
    #
    wph
    vk
    vx
    cA
    @0
    cV
    wph
    vk
    nfv
    #
    sge0xaddlem2.a
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    #
    cc0
    cpnf
    @0
    cc0
    cxr
    wcel
    @20
    0xr
    a1i
    cpnf
    cxr
    wcel
    @20
    pnfxr
    a1i
    @20
    @0
    @20
    cB
    cC
    @20
    cc0
    cpnf
    cico
    co
    #
    cr
    cB
    rge0ssre
    sge0xaddlem2.b
    sseldi
    #
    @20
    @21
    cr
    cC
    rge0ssre
    sge0xaddlem2.c
    sseldi
    #
    readdcld
    #
    rexrd
    @20
    cB
    cC
    @22
    @23
    @20
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cc0
    cB
    cle
    wbr
    @20
    @21
    @25
    cB
    cc0
    cpnf
    icossicc
    #
    sge0xaddlem2.b
    sseldi
    #
    cB
    xrge0ge0
    syl
    @20
    cC
    @25
    wcel
    #
    cc0
    cC
    cle
    wbr
    @20
    @21
    @25
    cC
    @27
    sge0xaddlem2.c
    sseldi
    #
    cC
    xrge0ge0
    syl
    addge0d
    @20
    @0
    @24
    ltpnfd
    elicod
    #
    sge0revalmpt
    #
    wph
    @11
    @1
    csumge0
    wph
    vk
    cA
    @10
    @0
    @20
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    @10
    @0
    wceq
    @22
    @23
    cB
    cC
    rexadd
    syl2anc
    #
    mpteq2dva
    fveq2d
    wph
    @16
    @13
    @15
    caddc
    co
    #
    vy
    @4
    vy
    cv
    #
    cB
    vk
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    vz
    @4
    vz
    cv
    #
    cC
    vk
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    caddc
    co
    #
    @9
    wph
    @13
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @16
    @36
    wceq
    sge0xaddlem2.sb
    sge0xaddlem2.sc
    @13
    @15
    rexadd
    syl2anc
    wph
    @13
    @41
    @15
    @46
    caddc
    wph
    vk
    vy
    cA
    cB
    cV
    @17
    sge0xaddlem2.a
    sge0xaddlem2.b
    sge0revalmpt
    #
    wph
    vk
    vz
    cA
    cC
    cV
    @17
    sge0xaddlem2.a
    sge0xaddlem2.c
    sge0revalmpt
    #
    oveq12d
    #
    wph
    @47
    @9
    wph
    @47
    wph
    @41
    @46
    wph
    @41
    @13
    cr
    wph
    @13
    @41
    @50
    eqcomd
    sge0xaddlem2.sb
    eqeltrd
    #
    wph
    @15
    @46
    cr
    @51
    sge0xaddlem2.sc
    eqeltrrd
    #
    readdcld
    rexrd
    #
    wph
    @8
    cxr
    wss
    #
    @9
    cxr
    wcel
    wph
    @6
    cxr
    wcel
    #
    vx
    @4
    wral
    @56
    wph
    @57
    vx
    @4
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @59
    @5
    @0
    vk
    @58
    @5
    cfn
    wcel
    wph
    @5
    @3
    cfn
    elinel2
    adantl
    #
    @59
    @18
    @5
    wcel
    #
    wa
    #
    cB
    cC
    @62
    wph
    @19
    @33
    wph
    @58
    @61
    simpll
    #
    @58
    @61
    @19
    wph
    @58
    @61
    wa
    @5
    cA
    @18
    @58
    @5
    cA
    wss
    @61
    @5
    cA
    cfn
    elpwinss
    adantr
    @58
    @61
    simpr
    sseldd
    adantll
    #
    @22
    syl2anc
    #
    @62
    wph
    @19
    @34
    @63
    @64
    @23
    syl2anc
    #
    readdcld
    fsumrecl
    rexrd
    ralrimiva
    vx
    @4
    @6
    cxr
    @7
    @7
    eqid
    rnmptss
    syl
    @8
    supxrcl
    syl
    #
    wph
    ve
    @47
    @9
    @55
    @67
    wph
    ve
    cv
    #
    crp
    wcel
    #
    wa
    #
    @47
    @36
    @9
    @68
    cxad
    co
    #
    cle
    wph
    @47
    @36
    wceq
    @69
    wph
    @36
    @47
    @52
    eqcomd
    adantr
    @70
    @13
    vu
    cv
    #
    cB
    vk
    csu
    #
    @68
    c2
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    vu
    @4
    wrex
    @36
    @71
    cle
    wbr
    #
    @70
    vk
    vu
    cA
    cB
    cV
    @74
    @70
    vk
    nfv
    #
    wph
    cA
    cV
    wcel
    #
    @69
    sge0xaddlem2.a
    adantr
    #
    wph
    @19
    @26
    @69
    @28
    adantlr
    @69
    @74
    crp
    wcel
    wph
    @68
    rphalfcl
    adantl
    #
    wph
    @48
    @69
    sge0xaddlem2.sb
    adantr
    sge0ltfirpmpt2
    @70
    @76
    @77
    vu
    @4
    @70
    @72
    @4
    wcel
    #
    @76
    @77
    @70
    @82
    @76
    w3a
    #
    @15
    vv
    cv
    #
    cC
    vk
    csu
    #
    @74
    caddc
    co
    #
    clt
    wbr
    #
    vv
    @4
    wrex
    #
    @77
    @70
    @82
    @88
    @76
    @70
    vk
    vv
    cA
    cC
    cV
    @74
    @78
    @80
    wph
    @19
    @29
    @69
    @30
    adantlr
    @81
    wph
    @49
    @69
    sge0xaddlem2.sc
    adantr
    sge0ltfirpmpt2
    3ad2ant1
    @83
    @87
    @77
    vv
    @4
    @83
    @84
    @4
    wcel
    #
    @87
    @77
    @83
    @89
    @87
    w3a
    #
    vj
    cA
    vk
    vj
    cv
    #
    cB
    csb
    #
    cmpt
    #
    csumge0
    cfv
    #
    vj
    cA
    vk
    @91
    cC
    csb
    #
    cmpt
    #
    csumge0
    cfv
    #
    caddc
    co
    #
    vx
    @4
    @5
    @92
    @95
    caddc
    co
    #
    vj
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @68
    cxad
    co
    #
    cle
    wbr
    @77
    @90
    vx
    cA
    @92
    @95
    @72
    vj
    @68
    cV
    @84
    @83
    @89
    @79
    @87
    @70
    @82
    @79
    @76
    @80
    3ad2ant1
    3ad2ant1
    @90
    @91
    cA
    wcel
    #
    wa
    #
    wph
    @105
    @92
    @21
    wcel
    #
    @83
    @89
    @105
    wph
    @87
    wph
    @69
    @82
    @76
    @105
    simpl1l
    3ad2antl1
    #
    @90
    @105
    simpr
    #
    @20
    cB
    @21
    wcel
    #
    wi
    wph
    @105
    wa
    #
    @107
    wi
    vk
    vj
    @111
    @107
    vk
    @111
    vk
    nfv
    #
    vk
    @92
    @21
    vk
    @91
    cB
    nfcsb1v
    #
    nfel1
    nfim
    @18
    @91
    wceq
    #
    @20
    @111
    @110
    @107
    @114
    @19
    @105
    wph
    @18
    @91
    cA
    eleq1
    anbi2d
    #
    @114
    cB
    @92
    @21
    vk
    @91
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    sge0xaddlem2.b
    chvar
    syl2anc
    @106
    wph
    @105
    @95
    @21
    wcel
    #
    @108
    @109
    @20
    cC
    @21
    wcel
    #
    wi
    @111
    @117
    wi
    vk
    vj
    @111
    @117
    vk
    @112
    vk
    @95
    @21
    vk
    @91
    cC
    nfcsb1v
    #
    nfel1
    nfim
    @114
    @20
    @111
    @118
    @117
    @115
    @114
    cC
    @95
    @21
    vk
    @91
    cC
    csbeq1a
    #
    eleq1d
    imbi12d
    sge0xaddlem2.c
    chvar
    syl2anc
    wph
    @69
    @82
    @76
    @89
    @87
    simp11r
    @90
    @82
    @72
    cA
    wss
    @70
    @82
    @76
    @89
    @87
    simp12
    @72
    cA
    cfn
    elpwinss
    syl
    @83
    @89
    @72
    cfn
    wcel
    #
    @87
    @82
    @70
    @121
    @76
    @72
    @3
    cfn
    elinel2
    3ad2ant2
    3ad2ant1
    @90
    @89
    @84
    cA
    wss
    @83
    @89
    @87
    simp2
    @84
    cA
    cfn
    elpwinss
    syl
    @89
    @83
    @84
    cfn
    wcel
    @87
    @84
    @3
    cfn
    elinel2
    3ad2ant2
    @90
    @76
    @94
    @72
    @92
    vj
    csu
    #
    @74
    caddc
    co
    #
    clt
    wbr
    #
    @70
    @82
    @76
    @89
    @87
    simp13
    @76
    @124
    @13
    @94
    @75
    @123
    clt
    @12
    @93
    csumge0
    vk
    vj
    cA
    cB
    @92
    vj
    cB
    nfcv
    #
    @113
    @116
    cbvmpt
    fveq2i
    #
    @73
    @122
    @74
    caddc
    @72
    cB
    @92
    vk
    vj
    @116
    vj
    @72
    nfcv
    vk
    @72
    nfcv
    @125
    @113
    cbvsum
    oveq1i
    breq12i
    biimpi
    syl
    @90
    @87
    @97
    @84
    @95
    vj
    csu
    #
    @74
    caddc
    co
    #
    clt
    wbr
    #
    @83
    @89
    @87
    simp3
    @87
    @129
    @15
    @97
    @86
    @128
    clt
    @14
    @96
    csumge0
    vk
    vj
    cA
    cC
    @95
    vj
    cC
    nfcv
    #
    @119
    @120
    cbvmpt
    fveq2i
    #
    @85
    @127
    @74
    caddc
    @84
    cC
    @95
    vk
    vj
    @120
    vj
    @84
    nfcv
    vk
    @84
    nfcv
    @130
    @119
    cbvsum
    oveq1i
    breq12i
    biimpi
    syl
    @90
    wph
    @103
    @25
    wcel
    wph
    @69
    @82
    @76
    @89
    @87
    simp11l
    #
    wph
    @103
    @2
    @25
    wph
    @103
    @9
    @2
    @103
    @9
    wceq
    wph
    @9
    @103
    cxr
    @8
    @102
    clt
    @7
    @101
    vx
    @4
    @6
    @100
    @5
    @0
    @99
    vk
    vj
    @114
    cB
    @92
    cC
    @95
    caddc
    @116
    @120
    oveq12d
    vj
    @5
    nfcv
    vk
    @5
    nfcv
    vj
    @0
    nfcv
    vk
    @92
    @95
    caddc
    @113
    vk
    caddc
    nfcv
    @119
    nfov
    cbvsum
    mpteq2i
    rneqi
    supeq1i
    #
    eqcomi
    a1i
    @32
    eqtr4d
    wph
    vk
    cA
    @0
    cV
    @17
    sge0xaddlem2.a
    @20
    @10
    @0
    @25
    @35
    @20
    @26
    @29
    @10
    @25
    wcel
    @28
    @30
    cB
    cC
    ge0xaddcl
    syl2anc
    eqeltrrd
    #
    sge0clmpt
    eqeltrd
    syl
    @90
    wph
    @94
    cr
    wcel
    @132
    wph
    @94
    @13
    cr
    @126
    sge0xaddlem2.sb
    syl5eqelr
    syl
    @90
    wph
    @97
    cr
    wcel
    @132
    wph
    @97
    @15
    cr
    @131
    sge0xaddlem2.sc
    syl5eqelr
    syl
    sge0xaddlem1
    @36
    @98
    @71
    @104
    cle
    @13
    @94
    @15
    @97
    caddc
    @126
    @131
    oveq12i
    @9
    @103
    @68
    cxad
    @133
    oveq1i
    breq12i
    sylibr
    3exp
    rexlimdv
    mpd
    3exp
    rexlimdv
    mpd
    eqbrtrd
    xrlexaddrp
    wph
    @9
    @2
    @47
    cle
    wph
    @2
    @9
    @32
    eqcomd
    wph
    @2
    @47
    cle
    wbr
    vk
    @5
    @0
    cmpt
    csumge0
    cfv
    #
    @47
    cle
    wbr
    #
    vx
    @4
    wral
    wph
    @136
    vx
    @4
    @59
    @135
    @5
    cB
    vk
    csu
    #
    @5
    cC
    vk
    csu
    #
    caddc
    co
    #
    @47
    cle
    @59
    @135
    @6
    @139
    @59
    @5
    @0
    vk
    @60
    @62
    wph
    @19
    @0
    @21
    wcel
    @63
    @64
    @31
    syl2anc
    sge0fsummpt
    @59
    @5
    cB
    cC
    vk
    @60
    @62
    cB
    @65
    recnd
    @62
    cC
    @66
    recnd
    fsumadd
    eqtrd
    @59
    @137
    @138
    @41
    @46
    @59
    @5
    cB
    vk
    @60
    @65
    fsumrecl
    #
    @59
    @5
    cC
    vk
    @60
    @66
    fsumrecl
    #
    wph
    @41
    cr
    wcel
    @58
    @53
    adantr
    wph
    @46
    cr
    wcel
    @58
    @54
    adantr
    @59
    @40
    cxr
    wss
    #
    @137
    @40
    wcel
    @137
    @41
    cle
    wbr
    wph
    @142
    @58
    wph
    @38
    cxr
    wcel
    #
    vy
    @4
    wral
    @142
    wph
    @143
    vy
    @4
    wph
    @37
    @4
    wcel
    #
    wa
    #
    @38
    @145
    @37
    cB
    vk
    @144
    @37
    cfn
    wcel
    wph
    @37
    @3
    cfn
    elinel2
    adantl
    @145
    @18
    @37
    wcel
    #
    wa
    wph
    @19
    @33
    wph
    @144
    @146
    simpll
    @144
    @146
    @19
    wph
    @144
    @146
    wa
    @37
    cA
    @18
    @144
    @37
    cA
    wss
    @146
    @37
    cA
    cfn
    elpwinss
    adantr
    @144
    @146
    simpr
    sseldd
    adantll
    @22
    syl2anc
    fsumrecl
    rexrd
    ralrimiva
    vy
    @4
    @38
    cxr
    @39
    @39
    eqid
    #
    rnmptss
    syl
    adantr
    @59
    vy
    @4
    @38
    @137
    @39
    cvv
    @147
    @59
    @58
    @137
    @137
    wceq
    #
    @137
    @38
    wceq
    #
    vy
    @4
    wrex
    wph
    @58
    simpr
    #
    @59
    @137
    eqidd
    @149
    @148
    vy
    @5
    @4
    @37
    @5
    wceq
    @38
    @137
    @137
    @37
    @5
    cB
    vk
    sumeq1
    eqeq2d
    rspcev
    syl2anc
    @59
    @137
    cr
    @140
    elexd
    elrnmptd
    @40
    @137
    supxrub
    syl2anc
    @59
    @45
    cxr
    wss
    #
    @138
    @45
    wcel
    @138
    @46
    cle
    wbr
    wph
    @151
    @58
    wph
    vz
    @4
    @43
    cxr
    @44
    wph
    vz
    nfv
    @44
    eqid
    #
    wph
    @42
    @4
    wcel
    #
    wa
    #
    @43
    @154
    @42
    cC
    vk
    @153
    @42
    cfn
    wcel
    wph
    @42
    @3
    cfn
    elinel2
    adantl
    @154
    @18
    @42
    wcel
    #
    wa
    wph
    @19
    @34
    wph
    @153
    @155
    simpll
    @153
    @155
    @19
    wph
    @153
    @155
    wa
    @42
    cA
    @18
    @153
    @42
    cA
    wss
    @155
    @42
    cA
    cfn
    elpwinss
    adantr
    @153
    @155
    simpr
    sseldd
    adantll
    @23
    syl2anc
    fsumrecl
    rexrd
    rnmptssd
    adantr
    @59
    vz
    @4
    @43
    @138
    @44
    cvv
    @152
    @59
    @58
    @138
    @138
    wceq
    #
    @138
    @43
    wceq
    #
    vz
    @4
    wrex
    @150
    @59
    @138
    eqidd
    @157
    @156
    vz
    @5
    @4
    @42
    @5
    wceq
    @43
    @138
    @138
    @42
    @5
    cC
    vk
    sumeq1
    eqeq2d
    rspcev
    syl2anc
    @59
    @138
    cr
    @141
    elexd
    elrnmptd
    @45
    @138
    supxrub
    syl2anc
    le2addd
    eqbrtrd
    ralrimiva
    wph
    vk
    vx
    cA
    @0
    @47
    cV
    @17
    sge0xaddlem2.a
    @134
    @55
    sge0lefimpt
    mpbird
    eqbrtrd
    xrletrid
    3eqtrd
    3eqtr4d
end
