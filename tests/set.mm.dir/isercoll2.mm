include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "cn.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "cz.mm"
include "wcel.mm"
include "1z.mm"
include "zsubcl.mm"
include "sylancr.mm"
include "seqex.mm"
include "a1i.mm"
include "wa.mm"
include "cuz.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "wceq.mm"
include "cfz.mm"
include "simpl.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "eluzelz.mm"
include "syl.mm"
include "zcnd.mm"
include "cc.mm"
include "1cnd.mm"
include "subadd23d.mm"
include "cn0.mm"
include "uznn0sub.mm"
include "nn0p1nn.mm"
include "eqeltrrd.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "oveq1d.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "pncan3d.mm"
include "eqtrd.mm"
include "eqtr2d.mm"
include "syl2an.mm"
include "seqshft2.mm"
include "pncan3.mm"
include "seqeq1d.mm"
include "fveq1d.mm"
include "climshft2.mm"
include "wf.mm"
include "uzid.mm"
include "nnm1nn0.mm"
include "uzaddcl.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "clt.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "breq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "nncn.mm"
include "adantl.mm"
include "addsubd.mm"
include "addassd.mm"
include "eqtr4d.mm"
include "breqtrrd.mm"
include "peano2nn.mm"
include "3brtr4d.mm"
include "crn.mm"
include "cdif.mm"
include "cc0.mm"
include "wss.mm"
include "wfn.mm"
include "ffn.mm"
include "wrex.mm"
include "eleq2s.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "frn.mm"
include "sscond.mm"
include "sselda.mm"
include "syldan.mm"
include "eqeq12d.mm"
include "3eqtr4d.mm"
include "isercoll.mm"
include "bitrd.mm"

theorem isercoll2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  assume isercoll2.z: |- Z = ( ZZ>= ` M )
  assume isercoll2.w: |- W = ( ZZ>= ` N )
  assume isercoll2.m: |- ( ph -> M e. ZZ )
  assume isercoll2.n: |- ( ph -> N e. ZZ )
  assume isercoll2.g: |- ( ph -> G : Z --> W )
  assume isercoll2.i: |- ( ( ph /\ k e. Z ) -> ( G ` k ) < ( G ` ( k + 1 ) ) )
  assume isercoll2.0: |- ( ( ph /\ n e. ( W \ ran G ) ) -> ( F ` n ) = 0 )
  assume isercoll2.f: |- ( ( ph /\ n e. W ) -> ( F ` n ) e. CC )
  assume isercoll2.h: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( F ` ( G ` k ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint G n
  disjoint H k
  disjoint H n
  disjoint N n
  disjoint M k
  disjoint M n
  disjoint k ph
  disjoint n ph
  disjoint W n
  disjoint Z k
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint F j
  disjoint j x
  disjoint G j
  disjoint k x
  disjoint n x
  disjoint G x
  disjoint H j
  disjoint H x
  disjoint N j
  disjoint M j
  disjoint M x
  disjoint j ph
  disjoint ph x
  disjoint W x
  disjoint Z j
  assert |- ( ph -> ( seq M ( + , H ) ~~> A <-> seq N ( + , F ) ~~> A ) )

  proof
    wph
    caddc
    cH
    cM
    cseq
    #
    cA
    cli
    wbr
    caddc
    vx
    cn
    cM
    vx
    cv
    #
    c1
    cmin
    co
    #
    caddc
    co
    #
    cH
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    cA
    cli
    wbr
    caddc
    cF
    cN
    cseq
    cA
    cli
    wbr
    wph
    cA
    vk
    @0
    @6
    c1
    cM
    cmin
    co
    #
    cM
    cvv
    cvv
    cZ
    isercoll2.z
    isercoll2.m
    wph
    c1
    cz
    wcel
    cM
    cz
    wcel
    #
    @7
    cz
    wcel
    #
    1z
    isercoll2.m
    c1
    cM
    zsubcl
    sylancr
    #
    @0
    cvv
    wcel
    wph
    caddc
    cH
    cM
    seqex
    a1i
    @6
    cvv
    wcel
    wph
    caddc
    @5
    c1
    seqex
    a1i
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @11
    @0
    cfv
    @11
    @7
    caddc
    co
    #
    caddc
    @5
    cM
    @7
    caddc
    co
    #
    cseq
    #
    cfv
    @14
    @6
    cfv
    @13
    caddc
    vj
    cH
    @5
    @7
    cM
    @11
    @13
    @11
    cZ
    cM
    cuz
    cfv
    #
    wph
    @12
    simpr
    isercoll2.z
    syl6eleq
    #
    wph
    @9
    @12
    @10
    adantr
    @13
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    @19
    cH
    cfv
    #
    @19
    @7
    caddc
    co
    #
    @5
    cfv
    #
    wceq
    @19
    cM
    @11
    cfz
    co
    wcel
    #
    wph
    @12
    simpl
    @24
    @19
    @17
    cZ
    @19
    cM
    @11
    elfzuz
    isercoll2.z
    syl6eleqr
    wph
    @20
    wa
    #
    @23
    cM
    @22
    c1
    cmin
    co
    #
    caddc
    co
    #
    cH
    cfv
    #
    @21
    @25
    @22
    cn
    wcel
    @23
    @28
    wceq
    @25
    @19
    cM
    cmin
    co
    #
    c1
    caddc
    co
    #
    @22
    cn
    @25
    @19
    cM
    c1
    @25
    @19
    @25
    @19
    @17
    wcel
    #
    @19
    cz
    wcel
    @25
    @19
    cZ
    @17
    wph
    @20
    simpr
    isercoll2.z
    syl6eleq
    #
    cM
    @19
    eluzelz
    syl
    zcnd
    #
    wph
    cM
    cc
    wcel
    #
    @20
    wph
    cM
    isercoll2.m
    zcnd
    #
    adantr
    #
    @25
    1cnd
    subadd23d
    #
    @25
    @29
    cn0
    wcel
    #
    @30
    cn
    wcel
    @25
    @31
    @38
    @32
    cM
    @19
    uznn0sub
    syl
    #
    @29
    nn0p1nn
    syl
    eqeltrrd
    vx
    @22
    @4
    @28
    cn
    @5
    @1
    @22
    wceq
    #
    @3
    @27
    cH
    @40
    @2
    @26
    cM
    caddc
    @1
    @22
    c1
    cmin
    oveq1
    oveq2d
    fveq2d
    @5
    eqid
    #
    @27
    cH
    fvex
    fvmpt
    syl
    @25
    @27
    @19
    cH
    @25
    @27
    cM
    @29
    caddc
    co
    @19
    @25
    @26
    @29
    cM
    caddc
    @25
    @30
    c1
    cmin
    co
    #
    @26
    @29
    @25
    @30
    @22
    c1
    cmin
    @37
    oveq1d
    @25
    @29
    cc
    wcel
    c1
    cc
    wcel
    #
    @42
    @29
    wceq
    @25
    @29
    @39
    nn0cnd
    ax-1cn
    @29
    c1
    pncan
    sylancl
    eqtr3d
    oveq2d
    @25
    cM
    @19
    @36
    @33
    pncan3d
    eqtrd
    fveq2d
    eqtr2d
    syl2an
    seqshft2
    @13
    @14
    @16
    @6
    @13
    @15
    c1
    caddc
    @5
    @13
    @34
    @43
    @15
    c1
    wceq
    wph
    @34
    @12
    @35
    adantr
    ax-1cn
    cM
    c1
    pncan3
    sylancl
    seqeq1d
    fveq1d
    eqtr2d
    climshft2
    wph
    cA
    vj
    vn
    cF
    vx
    cn
    @3
    cG
    cfv
    #
    cmpt
    #
    @5
    cN
    cW
    isercoll2.w
    isercoll2.n
    wph
    vx
    cn
    @44
    cW
    @45
    wph
    @1
    cn
    wcel
    #
    wa
    #
    cZ
    cW
    @3
    cG
    wph
    cZ
    cW
    cG
    wf
    #
    @46
    isercoll2.g
    adantr
    @47
    @3
    @17
    cZ
    wph
    cM
    @17
    wcel
    #
    @2
    cn0
    wcel
    @3
    @17
    wcel
    @46
    wph
    @8
    @49
    isercoll2.m
    cM
    uzid
    syl
    #
    @1
    nnm1nn0
    @2
    cM
    cM
    uzaddcl
    syl2an
    isercoll2.z
    syl6eleqr
    ffvelrnd
    @45
    eqid
    #
    fmptd
    wph
    @19
    cn
    wcel
    #
    wa
    #
    cM
    @19
    c1
    cmin
    co
    #
    caddc
    co
    #
    cG
    cfv
    #
    cM
    @19
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    caddc
    co
    #
    cG
    cfv
    #
    @19
    @45
    cfv
    #
    @57
    @45
    cfv
    #
    clt
    @53
    @56
    @55
    c1
    caddc
    co
    #
    cG
    cfv
    #
    @60
    clt
    @53
    @55
    cZ
    wcel
    #
    @11
    cG
    cfv
    #
    @11
    c1
    caddc
    co
    #
    cG
    cfv
    #
    clt
    wbr
    #
    vk
    cZ
    wral
    #
    @56
    @64
    clt
    wbr
    #
    @53
    @55
    @17
    cZ
    wph
    @49
    @54
    cn0
    wcel
    #
    @55
    @17
    wcel
    @52
    @50
    @19
    nnm1nn0
    #
    @54
    cM
    cM
    uzaddcl
    syl2an
    isercoll2.z
    syl6eleqr
    #
    wph
    @70
    @52
    wph
    @69
    vk
    cZ
    isercoll2.i
    ralrimiva
    adantr
    @69
    @71
    vk
    @55
    cZ
    @11
    @55
    wceq
    #
    @66
    @56
    @68
    @64
    clt
    @11
    @55
    cG
    fveq2
    #
    @75
    @67
    @63
    cG
    @11
    @55
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspcv
    sylc
    @53
    @59
    @63
    cG
    @53
    @59
    cM
    @54
    c1
    caddc
    co
    #
    caddc
    co
    @63
    @53
    @58
    @77
    cM
    caddc
    @53
    @19
    c1
    c1
    @52
    @19
    cc
    wcel
    wph
    @19
    nncn
    adantl
    @53
    1cnd
    #
    @78
    addsubd
    oveq2d
    @53
    cM
    @54
    c1
    wph
    @34
    @52
    @35
    adantr
    @53
    @54
    @52
    @72
    wph
    @73
    adantl
    nn0cnd
    @78
    addassd
    eqtr4d
    fveq2d
    breqtrrd
    @52
    @61
    @56
    wceq
    wph
    vx
    @19
    @44
    @56
    cn
    @45
    @1
    @19
    wceq
    #
    @3
    @55
    cG
    @79
    @2
    @54
    cM
    caddc
    @1
    @19
    c1
    cmin
    oveq1
    oveq2d
    #
    fveq2d
    @51
    @55
    cG
    fvex
    fvmpt
    adantl
    #
    @53
    @57
    cn
    wcel
    #
    @62
    @60
    wceq
    @52
    @82
    wph
    @19
    peano2nn
    adantl
    vx
    @57
    @44
    @60
    cn
    @45
    @1
    @57
    wceq
    #
    @3
    @59
    cG
    @83
    @2
    @58
    cM
    caddc
    @1
    @57
    c1
    cmin
    oveq1
    oveq2d
    fveq2d
    @51
    @59
    cG
    fvex
    fvmpt
    syl
    3brtr4d
    wph
    vn
    cv
    #
    cW
    @45
    crn
    #
    cdif
    #
    wcel
    @84
    cW
    cG
    crn
    #
    cdif
    #
    wcel
    @84
    cF
    cfv
    cc0
    wceq
    wph
    @86
    @88
    @84
    wph
    @87
    @85
    cW
    wph
    cZ
    @85
    cG
    wf
    #
    @87
    @85
    wss
    wph
    cG
    cZ
    wfn
    #
    @66
    @85
    wcel
    #
    vk
    cZ
    wral
    @89
    wph
    @48
    @90
    isercoll2.g
    cZ
    cW
    cG
    ffn
    syl
    wph
    @91
    vk
    cZ
    @13
    @66
    @44
    wceq
    #
    vx
    cn
    wrex
    #
    @91
    @13
    @11
    cM
    cmin
    co
    #
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @66
    cM
    @95
    c1
    cmin
    co
    #
    caddc
    co
    #
    cG
    cfv
    #
    wceq
    #
    @93
    @13
    @94
    cn0
    wcel
    #
    @96
    @13
    @11
    @17
    wcel
    @101
    @18
    cM
    @11
    uznn0sub
    syl
    #
    @94
    nn0p1nn
    syl
    @13
    @11
    @98
    cG
    @13
    @98
    cM
    @94
    caddc
    co
    #
    @11
    @13
    @97
    @94
    cM
    caddc
    @13
    @94
    cc
    wcel
    @43
    @97
    @94
    wceq
    @13
    @94
    @102
    nn0cnd
    ax-1cn
    @94
    c1
    pncan
    sylancl
    oveq2d
    wph
    @34
    @11
    cc
    wcel
    @103
    @11
    wceq
    @12
    @35
    @12
    @11
    @11
    cz
    wcel
    @11
    @17
    cZ
    cM
    @11
    eluzelz
    isercoll2.z
    eleq2s
    zcnd
    cM
    @11
    pncan3
    syl2an
    eqtr2d
    fveq2d
    @92
    @100
    vx
    @95
    cn
    @1
    @95
    wceq
    #
    @44
    @99
    @66
    @104
    @3
    @98
    cG
    @104
    @2
    @97
    cM
    caddc
    @1
    @95
    c1
    cmin
    oveq1
    oveq2d
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    @66
    cvv
    wcel
    @91
    @93
    wb
    @11
    cG
    fvex
    vx
    cn
    @44
    @66
    @45
    cvv
    @51
    elrnmpt
    ax-mp
    sylibr
    ralrimiva
    vk
    cZ
    @85
    cG
    ffnfv
    sylanbrc
    cZ
    @85
    cG
    frn
    syl
    sscond
    sselda
    isercoll2.0
    syldan
    isercoll2.f
    @53
    @55
    cH
    cfv
    #
    @56
    cF
    cfv
    #
    @19
    @5
    cfv
    #
    @61
    cF
    cfv
    @53
    @65
    @11
    cH
    cfv
    #
    @66
    cF
    cfv
    #
    wceq
    #
    vk
    cZ
    wral
    #
    @105
    @106
    wceq
    #
    @74
    wph
    @111
    @52
    wph
    @110
    vk
    cZ
    isercoll2.h
    ralrimiva
    adantr
    @110
    @112
    vk
    @55
    cZ
    @75
    @108
    @105
    @109
    @106
    @11
    @55
    cH
    fveq2
    @75
    @66
    @56
    cF
    @76
    fveq2d
    eqeq12d
    rspcv
    sylc
    @52
    @107
    @105
    wceq
    wph
    vx
    @19
    @4
    @105
    cn
    @5
    @79
    @3
    @55
    cH
    @80
    fveq2d
    @41
    @55
    cH
    fvex
    fvmpt
    adantl
    @53
    @61
    @56
    cF
    @81
    fveq2d
    3eqtr4d
    isercoll
    bitrd
end
