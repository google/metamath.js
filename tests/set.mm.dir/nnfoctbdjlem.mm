include "cn.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "wdisj.mm"
include "wa.mm"
include "wex.mm"
include "wf.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "wo.mm"
include "cif.mm"
include "iftrue.mm"
include "adantl.mm"
include "0ex.mm"
include "snid.mm"
include "elun2.mm"
include "ax-mp.mm"
include "syl6eqel.mm"
include "adantll.mm"
include "iffalse.mm"
include "wf1o.mm"
include "f1of.mm"
include "syl.mm"
include "adantr.mm"
include "pm2.46.mm"
include "notnotrd.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "elun1.mm"
include "eqeltrd.mm"
include "pm2.61dan.mm"
include "fmptd.mm"
include "crn.mm"
include "simpr.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "wb.mm"
include "wfn.mm"
include "ffnd.mm"
include "fvelrnb.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "caddc.mm"
include "sselda.mm"
include "peano2nnd.mm"
include "3adant3.mm"
include "cmpt.mm"
include "a1i.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "nnrpd.mm"
include "ltaddrp2d.mm"
include "id.mm"
include "breqtrd.mm"
include "gtned.mm"
include "neneqd.mm"
include "oveq1.mm"
include "nncnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "sylan9eqr.mm"
include "simplr.mm"
include "notnotd.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "iffalsed.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "ffvelrnda.mm"
include "fvmptd.mm"
include "simp3.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "reximdva.mm"
include "simpll.mm"
include "elunnel1.mm"
include "elsni.mm"
include "1nn.mm"
include "cvv.mm"
include "orcs.mm"
include "eqtr2d.mm"
include "eqeq2d.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "cin.mm"
include "animorrl.mm"
include "wne.mm"
include "fvmpt2.mm"
include "syldan.mm"
include "ineq1d.mm"
include "0in.mm"
include "syl6eq.mm"
include "ad4ant24.mm"
include "eqeq1.mm"
include "eleq1d.mm"
include "notbid.mm"
include "orbi12d.mm"
include "ifbieq2d.mm"
include "simpl.mm"
include "ineq2d.mm"
include "in0.mm"
include "ad5ant25.mm"
include "fvex.mm"
include "ifex.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "ad2antlr.mm"
include "fvexd.mm"
include "3adant2.mm"
include "ineq12d.mm"
include "ad5ant245.mm"
include "wf1.mm"
include "f1of1.mm"
include "dff14a.mm"
include "sylib.mm"
include "simprd.mm"
include "ad3antrrr.mm"
include "jca31.mm"
include "cc.mm"
include "nncn.mm"
include "subneintr2d.mm"
include "ad2antrr.mm"
include "neeq1.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "neeq2.mm"
include "neeq2d.mm"
include "rspc2va.mm"
include "sylc.mm"
include "ad4ant13.mm"
include "sylan2.mm"
include "ad4ant14.mm"
include "disjor.mm"
include "ineq1.mm"
include "eqeq2.mm"
include "ineq2.mm"
include "syl21anc.mm"
include "adantllr.mm"
include "orel1.mm"
include "olcd.mm"
include "pm2.61dane.mm"
include "ralrimivva.mm"
include "sylibr.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "foeq1.mm"
include "fveq1d.mm"
include "disjeq2dv.mm"
include "anbi12d.mm"
include "spcev.mm"

theorem nnfoctbdjlem
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vm: setvar m
  let vz: setvar z
  assume nnfoctbdjlem.a: |- ( ph -> A C_ NN )
  assume nnfoctbdjlem.g: |- ( ph -> G : A -1-1-onto-> X )
  assume nnfoctbdjlem.dj: |- ( ph -> Disj_ y e. X y )
  assume nnfoctbdjlem.f: |- F = ( n e. NN |-> if ( ( n = 1 \/ -. ( n - 1 ) e. A ) , (/) , ( G ` ( n - 1 ) ) ) )

  disjoint A n
  disjoint A y
  disjoint n y
  disjoint F f
  disjoint F n
  disjoint f n
  disjoint F y
  disjoint G n
  disjoint G y
  disjoint X f
  disjoint X n
  disjoint X y
  disjoint n ph
  disjoint ph y
  disjoint A k
  disjoint k n
  disjoint k y
  disjoint A x
  disjoint n x
  disjoint x y
  disjoint F k
  disjoint F m
  disjoint k m
  disjoint m n
  disjoint m y
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint n z
  disjoint y z
  disjoint X k
  disjoint X m
  disjoint X z
  disjoint m z
  disjoint k ph
  disjoint m ph
  disjoint k x
  assert |- ( ph -> E. f ( f : NN -onto-> ( X u. { (/) } ) /\ Disj_ n e. NN ( f ` n ) ) )

  proof
    wph
    cn
    cX
    c0
    csn
    #
    cun
    #
    cF
    wfo
    #
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    wdisj
    #
    cn
    @1
    vf
    cv
    #
    wfo
    #
    vn
    cn
    @3
    @6
    cfv
    #
    wdisj
    #
    wa
    #
    vf
    wex
    wph
    cn
    @1
    cF
    wf
    vy
    cv
    #
    vm
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vm
    cn
    wrex
    #
    vy
    @1
    wral
    @2
    wph
    vn
    cn
    @3
    c1
    wceq
    #
    @3
    c1
    cmin
    co
    #
    cA
    wcel
    #
    wn
    #
    wo
    #
    c0
    @17
    cG
    cfv
    #
    cif
    #
    @1
    cF
    wph
    @3
    cn
    wcel
    #
    wa
    #
    @20
    @22
    @1
    wcel
    #
    @23
    @20
    @25
    wph
    @23
    @20
    wa
    #
    @22
    c0
    @1
    @20
    @22
    c0
    wceq
    #
    @23
    @20
    c0
    @21
    iftrue
    #
    adantl
    #
    c0
    @0
    wcel
    c0
    @1
    wcel
    c0
    0ex
    snid
    c0
    @0
    cX
    elun2
    ax-mp
    syl6eqel
    adantll
    @24
    @20
    wn
    #
    wa
    #
    @22
    @21
    @1
    @30
    @22
    @21
    wceq
    @24
    @20
    c0
    @21
    iffalse
    #
    adantl
    @31
    @21
    cX
    wcel
    #
    @21
    @1
    wcel
    wph
    @30
    @33
    @23
    wph
    @30
    wa
    cA
    cX
    @17
    cG
    wph
    cA
    cX
    cG
    wf
    #
    @30
    wph
    cA
    cX
    cG
    wf1o
    #
    @34
    nnfoctbdjlem.g
    cA
    cX
    cG
    f1of
    syl
    #
    adantr
    @30
    @18
    wph
    @30
    @18
    @16
    @19
    pm2.46
    notnotrd
    #
    adantl
    ffvelrnd
    #
    adantlr
    @21
    cX
    @0
    elun1
    syl
    eqeltrd
    pm2.61dan
    nnfoctbdjlem.f
    fmptd
    wph
    @15
    vy
    @1
    wph
    @11
    @1
    wcel
    #
    wa
    #
    @11
    cX
    wcel
    #
    @15
    wph
    @41
    @15
    @39
    wph
    @41
    wa
    #
    @13
    @11
    wceq
    #
    vm
    cn
    wrex
    #
    @15
    @42
    vk
    cv
    #
    cG
    cfv
    #
    @11
    wceq
    #
    vk
    cA
    wrex
    #
    @44
    @42
    @11
    cG
    crn
    #
    wcel
    #
    @48
    @42
    @11
    cX
    @49
    wph
    @41
    simpr
    wph
    cX
    @49
    wceq
    @41
    wph
    @49
    cX
    wph
    @35
    cA
    cX
    cG
    wfo
    @49
    cX
    wceq
    nnfoctbdjlem.g
    cA
    cX
    cG
    f1ofo
    cA
    cX
    cG
    forn
    3syl
    eqcomd
    adantr
    eleqtrd
    wph
    @50
    @48
    wb
    #
    @41
    wph
    cG
    cA
    wfn
    @51
    wph
    cA
    cX
    cG
    @36
    ffnd
    vk
    cA
    @11
    cG
    fvelrnb
    syl
    adantr
    mpbid
    @42
    @47
    @44
    vk
    cA
    wph
    @45
    cA
    wcel
    #
    @47
    @44
    wi
    wi
    @41
    wph
    @52
    @47
    @44
    wph
    @52
    @47
    w3a
    #
    @45
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @54
    cF
    cfv
    #
    @11
    wceq
    #
    @44
    wph
    @52
    @55
    @47
    wph
    @52
    wa
    #
    @45
    wph
    cA
    cn
    @45
    nnfoctbdjlem.a
    sselda
    #
    peano2nnd
    #
    3adant3
    @53
    @56
    @46
    @11
    wph
    @52
    @56
    @46
    wceq
    @47
    @58
    vn
    @54
    @22
    @46
    cn
    cF
    cX
    cF
    vn
    cn
    @22
    cmpt
    #
    wceq
    #
    @58
    nnfoctbdjlem.f
    a1i
    @58
    @3
    @54
    wceq
    #
    wa
    #
    @22
    @21
    @46
    @64
    @20
    c0
    @21
    @64
    @16
    wn
    @19
    wn
    @30
    @64
    @3
    c1
    @64
    c1
    @3
    @64
    1red
    @64
    c1
    @54
    @3
    clt
    @58
    c1
    @54
    clt
    wbr
    @63
    @58
    c1
    @45
    @58
    1red
    @58
    @45
    @59
    nnrpd
    ltaddrp2d
    adantr
    @63
    @54
    @3
    wceq
    @58
    @63
    @3
    @54
    @63
    id
    eqcomd
    adantl
    breqtrd
    gtned
    neneqd
    @64
    @18
    @64
    @17
    @45
    cA
    @63
    @58
    @17
    @54
    c1
    cmin
    co
    @45
    @3
    @54
    c1
    cmin
    oveq1
    @58
    @45
    c1
    @58
    @45
    @59
    nncnd
    @58
    1cnd
    pncand
    sylan9eqr
    #
    wph
    @52
    @63
    simplr
    eqeltrd
    notnotd
    @16
    @19
    ioran
    sylanbrc
    iffalsed
    @64
    @17
    @45
    cG
    @65
    fveq2d
    eqtrd
    @60
    wph
    cA
    cX
    @45
    cG
    @36
    ffvelrnda
    fvmptd
    3adant3
    wph
    @52
    @47
    simp3
    eqtrd
    @43
    @57
    vm
    @54
    cn
    @12
    @54
    wceq
    @13
    @56
    @11
    @12
    @54
    cF
    fveq2
    eqeq1d
    rspcev
    syl2anc
    3exp
    adantr
    rexlimdv
    mpd
    @42
    @43
    @14
    vm
    cn
    @43
    @14
    wi
    @42
    @12
    cn
    wcel
    #
    wa
    @43
    @13
    @11
    @43
    id
    eqcomd
    a1i
    reximdva
    mpd
    adantlr
    @40
    @41
    wn
    #
    wa
    wph
    @11
    c0
    wceq
    #
    @15
    wph
    @39
    @67
    simpll
    @39
    @67
    @68
    wph
    @39
    @67
    wa
    @11
    @0
    wcel
    @68
    @11
    cX
    @0
    elunnel1
    @11
    c0
    elsni
    syl
    adantll
    wph
    @68
    wa
    #
    c1
    cn
    wcel
    #
    @11
    c1
    cF
    cfv
    #
    wceq
    #
    @15
    @70
    @69
    1nn
    a1i
    @69
    @71
    c0
    @11
    wph
    @71
    c0
    wceq
    @68
    wph
    vn
    c1
    @22
    c0
    cn
    cF
    cvv
    @62
    wph
    nnfoctbdjlem.f
    a1i
    @16
    @27
    wph
    @16
    @19
    @27
    @28
    orcs
    adantl
    @70
    wph
    1nn
    a1i
    c0
    cvv
    wcel
    wph
    0ex
    a1i
    fvmptd
    adantr
    @68
    c0
    @11
    wceq
    wph
    @68
    @11
    c0
    @68
    id
    eqcomd
    adantl
    eqtr2d
    @14
    @72
    vm
    c1
    cn
    @12
    c1
    wceq
    #
    @13
    @71
    @11
    @12
    c1
    cF
    fveq2
    eqeq2d
    rspcev
    syl2anc
    syl2anc
    pm2.61dan
    ralrimiva
    vm
    vy
    cn
    @1
    cF
    dffo3
    sylanbrc
    wph
    @3
    @12
    wceq
    #
    @4
    @13
    cin
    #
    c0
    wceq
    #
    wo
    #
    vm
    cn
    wral
    vn
    cn
    wral
    @5
    wph
    @77
    vn
    vm
    cn
    cn
    wph
    @23
    @66
    wa
    #
    wa
    #
    @77
    @3
    @12
    @79
    @74
    @76
    animorrl
    @79
    @3
    @12
    wne
    #
    wa
    #
    @76
    @74
    @81
    @20
    @76
    @78
    @20
    @76
    wph
    @80
    @23
    @20
    @76
    @66
    @26
    @75
    c0
    @13
    cin
    c0
    @26
    @4
    c0
    @13
    @26
    @4
    @22
    c0
    @23
    @20
    @22
    cvv
    wcel
    #
    @4
    @22
    wceq
    #
    @26
    @22
    c0
    cvv
    @29
    0ex
    syl6eqel
    vn
    cn
    @22
    cvv
    cF
    nnfoctbdjlem.f
    fvmpt2
    #
    syldan
    @29
    eqtrd
    ineq1d
    @13
    0in
    syl6eq
    adantlr
    ad4ant24
    @81
    @30
    wa
    #
    @73
    @12
    c1
    cmin
    co
    #
    cA
    wcel
    #
    wn
    #
    wo
    #
    @76
    @78
    @89
    @76
    wph
    @80
    @30
    @66
    @89
    @76
    @23
    @66
    @89
    wa
    #
    @75
    @4
    c0
    cin
    c0
    @90
    @13
    c0
    @4
    @90
    @13
    @89
    c0
    @86
    cG
    cfv
    #
    cif
    #
    c0
    @90
    vn
    @12
    @22
    @92
    cn
    cF
    cvv
    @62
    @90
    nnfoctbdjlem.f
    a1i
    @74
    @22
    @92
    wceq
    #
    @90
    @74
    @20
    @89
    @21
    @91
    c0
    @74
    @16
    @73
    @19
    @88
    @3
    @12
    c1
    eqeq1
    @74
    @18
    @87
    @74
    @17
    @86
    cA
    @3
    @12
    c1
    cmin
    oveq1
    #
    eleq1d
    notbid
    orbi12d
    @74
    @17
    @86
    cG
    @94
    fveq2d
    ifbieq2d
    #
    adantl
    @66
    @89
    simpl
    @89
    @92
    cvv
    wcel
    @66
    @89
    @92
    c0
    cvv
    @89
    c0
    @91
    iftrue
    #
    0ex
    syl6eqel
    adantl
    fvmptd
    @89
    @92
    c0
    wceq
    @66
    @96
    adantl
    eqtrd
    ineq2d
    @4
    in0
    syl6eq
    adantll
    ad5ant25
    @85
    @89
    wn
    #
    wa
    #
    @75
    @21
    @91
    cin
    #
    c0
    @78
    @30
    @97
    @75
    @99
    wceq
    wph
    @80
    @78
    @30
    @97
    w3a
    @4
    @21
    @13
    @91
    @78
    @30
    @4
    @21
    wceq
    #
    @97
    @23
    @30
    @100
    @66
    @23
    @30
    @4
    @22
    @21
    @23
    @82
    @83
    @20
    c0
    @21
    0ex
    @17
    cG
    fvex
    ifex
    @84
    mpan2
    @32
    sylan9eq
    adantlr
    3adant3
    @78
    @97
    @13
    @91
    wceq
    #
    @30
    @66
    @97
    @101
    @23
    @66
    @97
    wa
    #
    vn
    @12
    @22
    @91
    cn
    cF
    cvv
    @62
    @102
    nnfoctbdjlem.f
    a1i
    @102
    @74
    wa
    @22
    @92
    @91
    @74
    @93
    @102
    @95
    adantl
    @97
    @92
    @91
    wceq
    @66
    @74
    @89
    c0
    @91
    iffalse
    ad2antlr
    eqtrd
    @66
    @97
    simpl
    @102
    @86
    cG
    fvexd
    fvmptd
    adantll
    3adant2
    ineq12d
    ad5ant245
    @98
    @21
    @91
    wceq
    #
    wn
    @103
    @99
    c0
    wceq
    #
    wo
    #
    @104
    @98
    @21
    @91
    @98
    @18
    @87
    wa
    vx
    cv
    #
    @11
    wne
    #
    @106
    cG
    cfv
    #
    @11
    cG
    cfv
    #
    wne
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @17
    @86
    wne
    #
    @21
    @91
    wne
    #
    @98
    @18
    @87
    @112
    @30
    @18
    @81
    @97
    @37
    ad2antlr
    @97
    @87
    @85
    @97
    @87
    @73
    @88
    pm2.46
    notnotrd
    #
    adantl
    @79
    @112
    @80
    @30
    @97
    wph
    @112
    @78
    wph
    @34
    @112
    wph
    cA
    cX
    cG
    wf1
    #
    @34
    @112
    wa
    wph
    @35
    @116
    nnfoctbdjlem.g
    cA
    cX
    cG
    f1of1
    syl
    vx
    vy
    cA
    cX
    cG
    dff14a
    sylib
    simprd
    adantr
    ad3antrrr
    jca31
    @81
    @113
    @30
    @97
    @81
    @3
    @12
    c1
    @78
    @3
    cc
    wcel
    #
    wph
    @80
    @23
    @117
    @66
    @3
    nncn
    adantr
    ad2antlr
    @78
    @12
    cc
    wcel
    #
    wph
    @80
    @66
    @118
    @23
    @12
    nncn
    adantl
    ad2antlr
    @81
    1cnd
    @79
    @80
    simpr
    subneintr2d
    ad2antrr
    @111
    @113
    @114
    wi
    @17
    @11
    wne
    #
    @21
    @109
    wne
    #
    wi
    vx
    vy
    @17
    @86
    cA
    cA
    @106
    @17
    wceq
    #
    @107
    @119
    @110
    @120
    @106
    @17
    @11
    neeq1
    @121
    @108
    @21
    @109
    @106
    @17
    cG
    fveq2
    neeq1d
    imbi12d
    @11
    @86
    wceq
    #
    @119
    @113
    @120
    @114
    @11
    @86
    @17
    neeq2
    @122
    @109
    @91
    @21
    @11
    @86
    cG
    fveq2
    neeq2d
    imbi12d
    rspc2va
    sylc
    neneqd
    @79
    @30
    @97
    @105
    @80
    @79
    @30
    wa
    @97
    wa
    @33
    @91
    cX
    wcel
    #
    @11
    vz
    cv
    #
    wceq
    #
    @11
    @124
    cin
    #
    c0
    wceq
    #
    wo
    #
    vz
    cX
    wral
    vy
    cX
    wral
    #
    @105
    wph
    @30
    @33
    @78
    @97
    @38
    ad4ant13
    wph
    @97
    @123
    @78
    @30
    @97
    wph
    @87
    @123
    @115
    wph
    cA
    cX
    @86
    cG
    @36
    ffvelrnda
    sylan2
    ad4ant14
    wph
    @129
    @78
    @30
    @97
    wph
    vy
    cX
    @11
    wdisj
    @129
    nnfoctbdjlem.dj
    cX
    @11
    @124
    vy
    vz
    @125
    id
    disjor
    sylib
    ad3antrrr
    @128
    @105
    @21
    @124
    wceq
    #
    @21
    @124
    cin
    #
    c0
    wceq
    #
    wo
    vy
    vz
    @21
    @91
    cX
    cX
    @11
    @21
    wceq
    #
    @125
    @130
    @127
    @132
    @11
    @21
    @124
    eqeq1
    @133
    @126
    @131
    c0
    @11
    @21
    @124
    ineq1
    eqeq1d
    orbi12d
    @124
    @91
    wceq
    #
    @130
    @103
    @132
    @104
    @124
    @91
    @21
    eqeq2
    @134
    @131
    @99
    c0
    @124
    @91
    @21
    ineq2
    eqeq1d
    orbi12d
    rspc2va
    syl21anc
    adantllr
    @103
    @104
    orel1
    sylc
    eqtrd
    pm2.61dan
    pm2.61dan
    olcd
    pm2.61dane
    ralrimivva
    cn
    @4
    @13
    vn
    vm
    @3
    @12
    cF
    fveq2
    disjor
    sylibr
    @10
    @2
    @5
    wa
    vf
    cF
    cF
    @61
    cvv
    nnfoctbdjlem.f
    vn
    cn
    @22
    nnex
    mptex
    eqeltri
    @6
    cF
    wceq
    #
    @7
    @2
    @9
    @5
    cn
    @1
    @6
    cF
    foeq1
    @135
    vn
    cn
    @8
    @4
    @135
    @23
    wa
    @3
    @6
    cF
    @135
    @23
    simpl
    fveq1d
    disjeq2dv
    anbi12d
    spcev
    syl2anc
end
