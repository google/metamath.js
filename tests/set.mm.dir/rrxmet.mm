include "wcel.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "cme.mm"
include "cfv.mm"
include "csupp.mm"
include "cun.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "cfn.mm"
include "simprl.mm"
include "rrxfsupp.mm"
include "simprr.mm"
include "unfi.mm"
include "syl2anc.mm"
include "rrxsuppss.mm"
include "unssd.mm"
include "sselda.mm"
include "rrxf.mm"
include "ffvelrnda.mm"
include "resubcld.mm"
include "resqcld.mm"
include "syldan.mm"
include "fsumrecl.mm"
include "sqge0d.mm"
include "fsumge0.mm"
include "resqrtcld.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "rrxmfval.mm"
include "feq1d.mm"
include "mpbird.mm"
include "sqrt00.mm"
include "fsum00.mm"
include "cc.mm"
include "recnd.mm"
include "sqeq0.mm"
include "syl.mm"
include "subeq0ad.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "3bitrd.mm"
include "rrxmval.mm"
include "3expb.mm"
include "eqeq1d.mm"
include "wfn.mm"
include "ffnd.mm"
include "eqfnfv.mm"
include "cdif.mm"
include "wss.mm"
include "ssun1.mm"
include "a1i.mm"
include "simpl.mm"
include "0red.mm"
include "suppssr.mm"
include "ssun2.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "raldifeq.mm"
include "bitr4d.mm"
include "3bitr4d.mm"
include "w3a.mm"
include "3adant2.mm"
include "simp2.mm"
include "3expa.mm"
include "an32s.mm"
include "adantr.mm"
include "simpr.mm"
include "adantlr.mm"
include "trirn.mm"
include "npncand.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "fveq2d.mm"
include "sqsubswap.mm"
include "3brtr3d.mm"
include "simp1.mm"
include "rrxmetlem.mm"
include "eqtrd.mm"
include "3adant3r.mm"
include "3adant3l.mm"
include "oveq12d.mm"
include "sstri.mm"
include "3brtr4d.mm"
include "jca.mm"
include "cvv.mm"
include "cfsupp.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "ismet.mm"
include "ax-mp.mm"
include "sylanbrc.mm"

theorem rrxmet
  let cD: class D
  let vh: setvar h
  let cI: class I
  let cV: class V
  let cX: class X
  let cA: class A
  let vk: setvar k
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  assume rrxmval.1: |- X = { h e. ( RR ^m I ) | h finSupp 0 }
  assume rrxmval.d: |- D = ( dist ` ( RR^ ` I ) )

  disjoint I h
  disjoint V h
  disjoint A k
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F x
  disjoint f h
  disjoint f k
  disjoint g h
  disjoint g k
  disjoint h k
  disjoint h x
  disjoint k x
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G k
  disjoint G x
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h y
  disjoint h z
  disjoint k y
  disjoint k z
  disjoint V f
  disjoint V g
  disjoint V k
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( I e. V -> D e. ( Met ` X ) )

  proof
    cI
    cV
    wcel
    #
    cX
    cX
    cxp
    #
    cr
    cD
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    cc0
    wceq
    #
    @3
    @4
    wceq
    #
    wb
    #
    @5
    vz
    cv
    #
    @3
    cD
    co
    #
    @9
    @4
    cD
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    cD
    cX
    cme
    cfv
    wcel
    #
    @0
    @2
    @1
    cr
    vx
    vy
    cX
    cX
    @3
    cc0
    csupp
    co
    #
    @4
    cc0
    csupp
    co
    #
    cun
    #
    vk
    cv
    #
    @3
    cfv
    #
    @21
    @4
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cmpt2
    #
    wf
    #
    @0
    @27
    cr
    wcel
    #
    vy
    cX
    wral
    vx
    cX
    wral
    @29
    @0
    @30
    vx
    vy
    cX
    cX
    @0
    @3
    cX
    wcel
    #
    @4
    cX
    wcel
    #
    wa
    #
    wa
    #
    @26
    @34
    @20
    @25
    vk
    @34
    @18
    cfn
    wcel
    @19
    cfn
    wcel
    @20
    cfn
    wcel
    #
    @34
    vh
    @3
    cI
    cX
    rrxmval.1
    @0
    @31
    @32
    simprl
    #
    rrxfsupp
    @34
    vh
    @4
    cI
    cX
    rrxmval.1
    @0
    @31
    @32
    simprr
    #
    rrxfsupp
    @18
    @19
    unfi
    syl2anc
    #
    @34
    @21
    @20
    wcel
    #
    @21
    cI
    wcel
    #
    @25
    cr
    wcel
    @34
    @20
    cI
    @21
    @34
    @18
    @19
    cI
    @34
    vh
    @3
    cI
    cX
    rrxmval.1
    @36
    rrxsuppss
    @34
    vh
    @4
    cI
    cX
    rrxmval.1
    @37
    rrxsuppss
    unssd
    #
    sselda
    #
    @34
    @40
    wa
    #
    @24
    @43
    @22
    @23
    @34
    cI
    cr
    @21
    @3
    @34
    vh
    @3
    cI
    cX
    rrxmval.1
    @36
    rrxf
    #
    ffvelrnda
    #
    @34
    cI
    cr
    @21
    @4
    @34
    vh
    @4
    cI
    cX
    rrxmval.1
    @37
    rrxf
    #
    ffvelrnda
    #
    resubcld
    #
    resqcld
    syldan
    #
    fsumrecl
    #
    @34
    @20
    @25
    vk
    @38
    @49
    @34
    @39
    @40
    cc0
    @25
    cle
    wbr
    @42
    @43
    @24
    @48
    sqge0d
    syldan
    #
    fsumge0
    #
    resqrtcld
    ralrimivva
    vx
    vy
    cX
    cX
    @27
    cr
    @28
    @28
    eqid
    fmpt2
    sylib
    @0
    @1
    cr
    cD
    @28
    cD
    vx
    vy
    vh
    vk
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    rrxmfval
    feq1d
    mpbird
    @0
    @15
    vx
    vy
    cX
    cX
    @34
    @8
    @14
    @34
    @27
    cc0
    wceq
    #
    @22
    @23
    wceq
    #
    vk
    @20
    wral
    #
    @6
    @7
    @34
    @53
    @26
    cc0
    wceq
    #
    @25
    cc0
    wceq
    #
    vk
    @20
    wral
    @55
    @34
    @26
    cr
    wcel
    cc0
    @26
    cle
    wbr
    @53
    @56
    wb
    @50
    @52
    @26
    sqrt00
    syl2anc
    @34
    @20
    @25
    vk
    @38
    @49
    @51
    fsum00
    @34
    @57
    @54
    vk
    @20
    @34
    @39
    @40
    @57
    @54
    wb
    @42
    @43
    @57
    @24
    cc0
    wceq
    #
    @54
    @43
    @24
    cc
    wcel
    @57
    @58
    wb
    @43
    @24
    @48
    recnd
    @24
    sqeq0
    syl
    @43
    @22
    @23
    @43
    @22
    @45
    recnd
    #
    @43
    @23
    @47
    recnd
    #
    subeq0ad
    bitrd
    syldan
    ralbidva
    3bitrd
    @34
    @5
    @27
    cc0
    @0
    @31
    @32
    @5
    @27
    wceq
    #
    cD
    vh
    vk
    @3
    @4
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    rrxmval
    3expb
    #
    eqeq1d
    @34
    @7
    @54
    vk
    cI
    wral
    #
    @55
    @34
    @3
    cI
    wfn
    @4
    cI
    wfn
    @7
    @63
    wb
    @34
    cI
    cr
    @3
    @44
    ffnd
    @34
    cI
    cr
    @4
    @46
    ffnd
    vk
    cI
    @3
    @4
    eqfnfv
    syl2anc
    @34
    @54
    vk
    @20
    cI
    @41
    @34
    @54
    vk
    cI
    @20
    cdif
    #
    @34
    @21
    @64
    wcel
    wa
    @22
    cc0
    @23
    @34
    cI
    cr
    cr
    @3
    cV
    @20
    @21
    cc0
    @44
    @18
    @20
    wss
    @34
    @18
    @19
    ssun1
    #
    a1i
    @0
    @33
    simpl
    #
    @34
    0red
    #
    suppssr
    @34
    cI
    cr
    cr
    @4
    cV
    @20
    @21
    cc0
    @46
    @19
    @20
    wss
    @34
    @19
    @18
    ssun2
    #
    a1i
    @66
    @67
    suppssr
    eqtr4d
    ralrimiva
    raldifeq
    bitr4d
    3bitr4d
    @34
    @13
    vz
    cX
    @34
    @9
    cX
    wcel
    #
    wa
    #
    @20
    @9
    cc0
    csupp
    co
    #
    cun
    #
    @25
    vk
    csu
    #
    csqrt
    cfv
    #
    @72
    @21
    @9
    cfv
    #
    @22
    cmin
    co
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    @72
    @75
    @23
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    @5
    @12
    cle
    @70
    @72
    @22
    @75
    cmin
    co
    #
    @79
    caddc
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    @72
    @84
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    @82
    caddc
    co
    @74
    @83
    cle
    @70
    @72
    @84
    @79
    vk
    @0
    @69
    @33
    @72
    cfn
    wcel
    #
    @0
    @69
    @33
    @91
    @0
    @69
    @33
    w3a
    #
    @35
    @71
    cfn
    wcel
    @91
    @0
    @33
    @35
    @69
    @38
    3adant2
    @92
    vh
    @9
    cI
    cX
    rrxmval.1
    @0
    @69
    @33
    simp2
    #
    rrxfsupp
    @20
    @71
    unfi
    syl2anc
    #
    3expa
    an32s
    @70
    @21
    @72
    wcel
    #
    @40
    @84
    cr
    wcel
    @70
    @72
    cI
    @21
    @70
    @20
    @71
    cI
    @34
    @20
    cI
    wss
    @69
    @41
    adantr
    @70
    vh
    @9
    cI
    cX
    rrxmval.1
    @34
    @69
    simpr
    #
    rrxsuppss
    unssd
    sselda
    #
    @70
    @40
    wa
    #
    @22
    @75
    @34
    @40
    @22
    cr
    wcel
    @69
    @45
    adantlr
    @70
    cI
    cr
    @21
    @9
    @70
    vh
    @9
    cI
    cX
    rrxmval.1
    @96
    rrxf
    ffvelrnda
    #
    resubcld
    syldan
    @70
    @95
    @40
    @79
    cr
    wcel
    @97
    @98
    @75
    @23
    @99
    @34
    @40
    @23
    cr
    wcel
    @69
    @47
    adantlr
    resubcld
    syldan
    trirn
    @70
    @87
    @73
    csqrt
    @70
    @72
    @86
    @25
    vk
    @70
    @95
    @40
    @86
    @25
    wceq
    @97
    @98
    @85
    @24
    c2
    cexp
    @98
    @22
    @75
    @23
    @34
    @40
    @22
    cc
    wcel
    #
    @69
    @59
    adantlr
    #
    @98
    @75
    @99
    recnd
    #
    @34
    @40
    @23
    cc
    wcel
    @69
    @60
    adantlr
    npncand
    oveq1d
    syldan
    sumeq2dv
    fveq2d
    @70
    @90
    @78
    @82
    caddc
    @70
    @89
    @77
    csqrt
    @70
    @72
    @88
    @76
    vk
    @70
    @95
    @40
    @88
    @76
    wceq
    #
    @97
    @98
    @100
    @75
    cc
    wcel
    @103
    @101
    @102
    @22
    @75
    sqsubswap
    syl2anc
    syldan
    sumeq2dv
    fveq2d
    oveq1d
    3brtr3d
    @70
    @5
    @27
    @74
    @34
    @61
    @69
    @62
    adantr
    @0
    @69
    @33
    @27
    @74
    wceq
    #
    @0
    @69
    @33
    @104
    @92
    @26
    @73
    csqrt
    @92
    @72
    cD
    vh
    vk
    @3
    @4
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    @0
    @69
    @33
    simp1
    #
    @0
    @33
    @31
    @69
    @36
    3adant2
    #
    @0
    @33
    @32
    @69
    @37
    3adant2
    #
    @92
    @20
    @71
    cI
    @92
    @18
    @19
    cI
    @92
    vh
    @3
    cI
    cX
    rrxmval.1
    @106
    rrxsuppss
    @92
    vh
    @4
    cI
    cX
    rrxmval.1
    @107
    rrxsuppss
    unssd
    @92
    vh
    @9
    cI
    cX
    rrxmval.1
    @93
    rrxsuppss
    unssd
    #
    @94
    @20
    @72
    wss
    @92
    @20
    @71
    ssun1
    #
    a1i
    rrxmetlem
    fveq2d
    3expa
    an32s
    eqtrd
    @0
    @69
    @33
    @12
    @83
    wceq
    #
    @0
    @69
    @33
    @110
    @92
    @12
    @71
    @18
    cun
    @76
    vk
    csu
    #
    csqrt
    cfv
    #
    @71
    @19
    cun
    @80
    vk
    csu
    #
    csqrt
    cfv
    #
    caddc
    co
    @83
    @92
    @10
    @112
    @11
    @114
    caddc
    @0
    @69
    @31
    @10
    @112
    wceq
    @32
    cD
    vh
    vk
    @9
    @3
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    rrxmval
    3adant3r
    @0
    @69
    @32
    @11
    @114
    wceq
    @31
    cD
    vh
    vk
    @9
    @4
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    rrxmval
    3adant3l
    oveq12d
    @92
    @112
    @78
    @114
    @82
    caddc
    @92
    @111
    @77
    csqrt
    @92
    @72
    cD
    vh
    vk
    @9
    @3
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    @105
    @93
    @106
    @108
    @94
    @92
    @71
    @18
    @72
    @71
    @72
    wss
    @92
    @71
    @20
    ssun2
    a1i
    #
    @18
    @72
    wss
    @92
    @18
    @20
    @72
    @65
    @109
    sstri
    a1i
    unssd
    rrxmetlem
    fveq2d
    @92
    @113
    @81
    csqrt
    @92
    @72
    cD
    vh
    vk
    @9
    @4
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    @105
    @93
    @107
    @108
    @94
    @92
    @71
    @19
    @72
    @115
    @19
    @72
    wss
    @92
    @19
    @20
    @72
    @68
    @109
    sstri
    a1i
    unssd
    rrxmetlem
    fveq2d
    oveq12d
    eqtrd
    3expa
    an32s
    3brtr4d
    ralrimiva
    jca
    ralrimivva
    cX
    cvv
    wcel
    @17
    @2
    @16
    wa
    wb
    vh
    cv
    cc0
    cfsupp
    wbr
    vh
    cr
    cI
    cmap
    co
    cX
    rrxmval.1
    cr
    cI
    cmap
    ovex
    rabex2
    vx
    vy
    vz
    cvv
    cD
    cX
    ismet
    ax-mp
    sylanbrc
end
