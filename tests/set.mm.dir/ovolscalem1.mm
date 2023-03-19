include "covol.mm"
include "cfv.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "crab.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "ovolcl.mm"
include "syl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cn.mm"
include "wf.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "simp3d.mm"
include "wb.mm"
include "simp1d.mm"
include "simp2d.mm"
include "rpregt0d.mm"
include "adantr.mm"
include "lediv1.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "df-br.mm"
include "sylib.mm"
include "crp.mm"
include "rerpdivcld.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "elind.mm"
include "fmptd.mm"
include "eqid.mm"
include "ovolsf.mm"
include "frn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "rpred.mm"
include "readdcld.mm"
include "rexrd.mm"
include "cioo.mm"
include "cuni.mm"
include "wrex.mm"
include "wral.mm"
include "eleq2d.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "simprr.mm"
include "ovolfioo.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "cvv.mm"
include "opex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "fveq2d.mm"
include "ovex.mm"
include "op1st.mm"
include "syl6eq.mm"
include "adantl.mm"
include "breq1d.mm"
include "adantlr.mm"
include "simplrl.mm"
include "ltdivmul.mm"
include "bitr2d.mm"
include "ltmuldiv2.mm"
include "op2nd.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "mpbird.mm"
include "ovollb.mm"
include "cfz.mm"
include "csu.mm"
include "fzfid.mm"
include "cc.mm"
include "rpcnd.mm"
include "simpl.mm"
include "elfznn.mm"
include "resubcld.mm"
include "syl2an.mm"
include "recnd.mm"
include "wne.mm"
include "rpne0d.mm"
include "fsumdivc.mm"
include "oveq12d.mm"
include "ovolfsval.mm"
include "rpcnne0d.mm"
include "divsubdir.mm"
include "3eqtr4d.mm"
include "cuz.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fsumser.mm"
include "eqtrd.mm"
include "rpmulcld.mm"
include "supxrleub.mm"
include "wfn.mm"
include "ffn.mm"
include "ralrn.mm"
include "r19.21bi.mm"
include "fveq1i.mm"
include "syl6eqr.mm"
include "adddid.mm"
include "divcan2d.mm"
include "oveq1d.mm"
include "3brtr4d.mm"
include "fsumrecl.mm"
include "ledivmul.mm"
include "eqbrtrrd.mm"
include "ralrimiva.mm"
include "xrletrd.mm"

theorem ovolscalem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vk: setvar k
  let vy: setvar y
  let vm: setvar m
  assume ovolsca.1: |- ( ph -> A C_ RR )
  assume ovolsca.2: |- ( ph -> C e. RR+ )
  assume ovolsca.3: |- ( ph -> B = { x e. RR | ( C x. x ) e. A } )
  assume ovolsca.4: |- ( ph -> ( vol* ` A ) e. RR )
  assume ovolsca.5: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovolsca.6: |- G = ( n e. NN |-> <. ( ( 1st ` ( F ` n ) ) / C ) , ( ( 2nd ` ( F ` n ) ) / C ) >. )
  assume ovolsca.7: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ovolsca.8: |- ( ph -> A C_ U. ran ( (,) o. F ) )
  assume ovolsca.9: |- ( ph -> R e. RR+ )
  assume ovolsca.10: |- ( ph -> sup ( ran S , RR* , < ) <_ ( ( vol* ` A ) + ( C x. R ) ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B n
  disjoint F n
  disjoint F x
  disjoint G n
  disjoint R x
  disjoint C n
  disjoint C x
  disjoint n ph
  disjoint S x
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint B f
  disjoint B y
  disjoint G k
  disjoint G y
  disjoint R k
  disjoint R y
  disjoint f m
  disjoint C f
  disjoint k m
  disjoint C k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint C m
  disjoint C y
  disjoint f ph
  disjoint k ph
  disjoint ph y
  disjoint S k
  assert |- ( ph -> ( vol* ` B ) <_ ( ( ( vol* ` A ) / C ) + R ) )

  proof
    wph
    cB
    covol
    cfv
    #
    caddc
    cabs
    cmin
    ccom
    #
    cG
    ccom
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    cA
    covol
    cfv
    #
    cC
    cdiv
    co
    #
    cR
    caddc
    co
    #
    wph
    cB
    cr
    wss
    #
    @0
    cxr
    wcel
    wph
    cB
    cC
    vx
    cv
    #
    cmul
    co
    #
    cA
    wcel
    #
    vx
    cr
    crab
    #
    cr
    ovolsca.3
    @12
    vx
    cr
    ssrab2
    syl6eqss
    #
    cB
    ovolcl
    syl
    wph
    @4
    cxr
    wss
    #
    @5
    cxr
    wcel
    wph
    @4
    cc0
    cpnf
    cico
    co
    #
    cxr
    wph
    cn
    @16
    @3
    wf
    #
    @4
    @16
    wss
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cG
    wf
    #
    @17
    wph
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    cC
    cdiv
    co
    #
    @22
    c2nd
    cfv
    #
    cC
    cdiv
    co
    #
    cop
    #
    @19
    cG
    wph
    @21
    cn
    wcel
    #
    wa
    #
    cle
    @18
    @27
    @29
    @24
    @26
    cle
    wbr
    #
    @27
    cle
    wcel
    @29
    @23
    @25
    cle
    wbr
    #
    @30
    @29
    @23
    cr
    wcel
    #
    @25
    cr
    wcel
    #
    @31
    wph
    cn
    @19
    cF
    wf
    #
    @28
    @32
    @33
    @31
    w3a
    ovolsca.7
    cF
    @21
    ovolfcl
    sylan
    #
    simp3d
    @29
    @32
    @33
    cC
    cr
    wcel
    cc0
    cC
    clt
    wbr
    wa
    #
    @31
    @30
    wb
    @29
    @32
    @33
    @31
    @35
    simp1d
    #
    @29
    @32
    @33
    @31
    @35
    simp2d
    #
    wph
    @36
    @28
    wph
    cC
    ovolsca.2
    rpregt0d
    #
    adantr
    #
    @23
    @25
    cC
    lediv1
    syl3anc
    mpbid
    @24
    @26
    cle
    df-br
    sylib
    @29
    @24
    cr
    wcel
    @26
    cr
    wcel
    @27
    @18
    wcel
    @29
    @23
    cC
    @37
    wph
    cC
    crp
    wcel
    @28
    ovolsca.2
    adantr
    #
    rerpdivcld
    @29
    @25
    cC
    @38
    @41
    rerpdivcld
    @24
    @26
    cr
    cr
    opelxpi
    syl2anc
    elind
    ovolsca.6
    fmptd
    #
    @3
    cG
    @2
    @2
    eqid
    #
    @3
    eqid
    #
    ovolsf
    syl
    #
    cn
    @16
    @3
    frn
    syl
    cc0
    cpnf
    icossxr
    #
    syl6ss
    #
    @4
    supxrcl
    syl
    wph
    @8
    wph
    @7
    cR
    wph
    @6
    cC
    ovolsca.4
    ovolsca.2
    rerpdivcld
    #
    wph
    cR
    ovolsca.9
    rpred
    readdcld
    #
    rexrd
    #
    wph
    @20
    cB
    cioo
    cG
    ccom
    crn
    cuni
    wss
    #
    @0
    @5
    cle
    wbr
    @42
    wph
    @51
    @21
    cG
    cfv
    #
    c1st
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @54
    @52
    c2nd
    cfv
    #
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vy
    cB
    wral
    #
    wph
    @59
    vy
    cB
    wph
    @54
    cB
    wcel
    #
    @54
    cr
    wcel
    #
    cC
    @54
    cmul
    co
    #
    cA
    wcel
    #
    wa
    #
    @59
    wph
    @61
    @54
    @13
    wcel
    @65
    wph
    cB
    @13
    @54
    ovolsca.3
    eleq2d
    @12
    @64
    vx
    @54
    cr
    @10
    @54
    wceq
    @11
    @63
    cA
    @10
    @54
    cC
    cmul
    oveq2
    eleq1d
    elrab
    syl6bb
    wph
    @65
    @59
    wph
    @65
    wa
    #
    @23
    @63
    clt
    wbr
    #
    @63
    @25
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    @59
    @66
    @64
    @23
    @10
    clt
    wbr
    #
    @10
    @25
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vx
    cA
    wral
    #
    @70
    wph
    @62
    @64
    simprr
    wph
    @75
    @65
    wph
    cA
    cioo
    cF
    ccom
    crn
    cuni
    wss
    #
    @75
    ovolsca.8
    wph
    cA
    cr
    wss
    @34
    @76
    @75
    wb
    ovolsca.1
    ovolsca.7
    vx
    cA
    vn
    cF
    ovolfioo
    syl2anc
    mpbid
    adantr
    @74
    @70
    vx
    @63
    cA
    @10
    @63
    wceq
    #
    @73
    @69
    vn
    cn
    @77
    @71
    @67
    @72
    @68
    @10
    @63
    @23
    clt
    breq2
    @10
    @63
    @25
    clt
    breq1
    anbi12d
    rexbidv
    rspcv
    sylc
    @66
    @69
    @58
    vn
    cn
    @66
    @28
    wa
    #
    @67
    @55
    @68
    @57
    @78
    @55
    @24
    @54
    clt
    wbr
    #
    @67
    @78
    @53
    @24
    @54
    clt
    @28
    @53
    @24
    wceq
    @66
    @28
    @53
    @27
    c1st
    cfv
    @24
    @28
    @52
    @27
    c1st
    @28
    @27
    cvv
    wcel
    @52
    @27
    wceq
    @24
    @26
    opex
    vn
    cn
    @27
    cvv
    cG
    ovolsca.6
    fvmpt2
    mpan2
    #
    fveq2d
    @24
    @26
    @23
    cC
    cdiv
    ovex
    #
    @25
    cC
    cdiv
    ovex
    #
    op1st
    syl6eq
    #
    adantl
    breq1d
    @78
    @32
    @62
    @36
    @79
    @67
    wb
    wph
    @28
    @32
    @65
    @37
    adantlr
    wph
    @62
    @64
    @28
    simplrl
    #
    wph
    @28
    @36
    @65
    @40
    adantlr
    #
    @23
    @54
    cC
    ltdivmul
    syl3anc
    bitr2d
    @78
    @68
    @54
    @26
    clt
    wbr
    #
    @57
    @78
    @62
    @33
    @36
    @68
    @86
    wb
    @84
    wph
    @28
    @33
    @65
    @38
    adantlr
    @85
    @54
    @25
    cC
    ltmuldiv2
    syl3anc
    @78
    @56
    @26
    @54
    clt
    @28
    @56
    @26
    wceq
    @66
    @28
    @56
    @27
    c2nd
    cfv
    @26
    @28
    @52
    @27
    c2nd
    @80
    fveq2d
    @24
    @26
    @81
    @82
    op2nd
    syl6eq
    #
    adantl
    breq2d
    bitr4d
    anbi12d
    rexbidva
    mpbid
    ex
    sylbid
    ralrimiv
    wph
    @9
    @20
    @51
    @60
    wb
    @14
    @42
    vy
    cB
    vn
    cG
    ovolfioo
    syl2anc
    mpbird
    cB
    @3
    cG
    @44
    ovollb
    syl2anc
    wph
    @5
    @8
    cle
    wbr
    #
    @54
    @8
    cle
    wbr
    #
    vy
    @4
    wral
    #
    wph
    @90
    vk
    cv
    #
    @3
    cfv
    #
    @8
    cle
    wbr
    #
    vk
    cn
    wral
    #
    wph
    @93
    vk
    cn
    wph
    @91
    cn
    wcel
    #
    wa
    #
    c1
    @91
    cfz
    co
    #
    @25
    @23
    cmin
    co
    #
    vn
    csu
    #
    cC
    cdiv
    co
    #
    @92
    @8
    cle
    @96
    @100
    @97
    @98
    cC
    cdiv
    co
    #
    vn
    csu
    @92
    @96
    @97
    @98
    cC
    vn
    @96
    c1
    @91
    fzfid
    #
    wph
    cC
    cc
    wcel
    #
    @95
    wph
    cC
    ovolsca.2
    rpcnd
    #
    adantr
    @96
    @21
    @97
    wcel
    #
    wa
    @98
    @96
    wph
    @28
    @98
    cr
    wcel
    @105
    wph
    @95
    simpl
    #
    @21
    @91
    elfznn
    #
    @29
    @25
    @23
    @38
    @37
    resubcld
    #
    syl2an
    #
    recnd
    #
    wph
    cC
    cc0
    wne
    #
    @95
    wph
    cC
    ovolsca.2
    rpne0d
    #
    adantr
    fsumdivc
    @96
    @101
    vn
    @2
    c1
    @91
    @96
    wph
    @28
    @21
    @2
    cfv
    #
    @101
    wceq
    @105
    @106
    @107
    @29
    @56
    @53
    cmin
    co
    #
    @26
    @24
    cmin
    co
    #
    @113
    @101
    @28
    @114
    @115
    wceq
    wph
    @28
    @56
    @26
    @53
    @24
    cmin
    @87
    @83
    oveq12d
    adantl
    wph
    @20
    @28
    @113
    @114
    wceq
    @42
    cG
    @2
    @21
    @43
    ovolfsval
    sylan
    @29
    @25
    cc
    wcel
    @23
    cc
    wcel
    @103
    @111
    wa
    #
    @101
    @115
    wceq
    @29
    @25
    @38
    recnd
    @29
    @23
    @37
    recnd
    wph
    @116
    @28
    wph
    cC
    ovolsca.2
    rpcnne0d
    adantr
    @25
    @23
    cC
    divsubdir
    syl3anc
    3eqtr4d
    syl2an
    @96
    @91
    cn
    c1
    cuz
    cfv
    wph
    @95
    simpr
    nnuz
    syl6eleq
    #
    @96
    wph
    @28
    @101
    cc
    wcel
    @105
    @106
    @107
    @29
    @101
    @29
    @98
    cC
    @108
    @41
    rerpdivcld
    recnd
    syl2an
    fsumser
    eqtrd
    @96
    @100
    @8
    cle
    wbr
    #
    @99
    cC
    @8
    cmul
    co
    #
    cle
    wbr
    #
    @96
    @91
    cS
    cfv
    #
    @6
    cC
    cR
    cmul
    co
    #
    caddc
    co
    #
    @99
    @119
    cle
    wph
    @121
    @123
    cle
    wbr
    #
    vk
    cn
    wph
    @10
    @123
    cle
    wbr
    #
    vx
    cS
    crn
    #
    wral
    #
    @124
    vk
    cn
    wral
    #
    wph
    @126
    cxr
    clt
    csup
    @123
    cle
    wbr
    #
    @127
    ovolsca.10
    wph
    @126
    cxr
    wss
    @123
    cxr
    wcel
    @129
    @127
    wb
    wph
    @126
    @16
    cxr
    wph
    cn
    @16
    cS
    wf
    #
    @126
    @16
    wss
    wph
    @34
    @130
    ovolsca.7
    cS
    cF
    @1
    cF
    ccom
    #
    @131
    eqid
    #
    ovolsca.5
    ovolsf
    syl
    #
    cn
    @16
    cS
    frn
    syl
    @46
    syl6ss
    wph
    @123
    wph
    @6
    @122
    ovolsca.4
    wph
    @122
    wph
    cC
    cR
    ovolsca.2
    ovolsca.9
    rpmulcld
    rpred
    readdcld
    rexrd
    vx
    @126
    @123
    supxrleub
    syl2anc
    mpbid
    wph
    cS
    cn
    wfn
    #
    @127
    @128
    wb
    wph
    @130
    @134
    @133
    cn
    @16
    cS
    ffn
    syl
    @125
    @124
    vx
    vk
    cn
    cS
    @10
    @121
    @123
    cle
    breq1
    ralrn
    syl
    mpbid
    r19.21bi
    @96
    @99
    @91
    caddc
    @131
    c1
    cseq
    #
    cfv
    @121
    @96
    @98
    vn
    @131
    c1
    @91
    @96
    @34
    @28
    @21
    @131
    cfv
    @98
    wceq
    @105
    wph
    @34
    @95
    ovolsca.7
    adantr
    @107
    cF
    @131
    @21
    @132
    ovolfsval
    syl2an
    @117
    @110
    fsumser
    @91
    cS
    @135
    ovolsca.5
    fveq1i
    syl6eqr
    wph
    @119
    @123
    wceq
    @95
    wph
    @119
    cC
    @7
    cmul
    co
    #
    @122
    caddc
    co
    @123
    wph
    cC
    @7
    cR
    @104
    wph
    @7
    @48
    recnd
    wph
    cR
    ovolsca.9
    rpcnd
    adddid
    wph
    @136
    @6
    @122
    caddc
    wph
    @6
    cC
    wph
    @6
    ovolsca.4
    recnd
    @104
    @112
    divcan2d
    oveq1d
    eqtrd
    adantr
    3brtr4d
    @96
    @99
    cr
    wcel
    @8
    cr
    wcel
    #
    @36
    @118
    @120
    wb
    @96
    @97
    @98
    vn
    @102
    @109
    fsumrecl
    wph
    @137
    @95
    @49
    adantr
    wph
    @36
    @95
    @39
    adantr
    @99
    @8
    cC
    ledivmul
    syl3anc
    mpbird
    eqbrtrrd
    ralrimiva
    wph
    @3
    cn
    wfn
    #
    @90
    @94
    wb
    wph
    @17
    @138
    @45
    cn
    @16
    @3
    ffn
    syl
    @89
    @93
    vy
    vk
    cn
    @3
    @54
    @92
    @8
    cle
    breq1
    ralrn
    syl
    mpbird
    wph
    @15
    @8
    cxr
    wcel
    @88
    @90
    wb
    @47
    @50
    vy
    @4
    @8
    supxrleub
    syl2anc
    mpbird
    xrletrd
end
