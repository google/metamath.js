include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "wcel.mm"
include "wceq.mm"
include "csn.mm"
include "eldifad.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "sumex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cmpt.mm"
include "nn0uz.mm"
include "0zd.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "adantl.mm"
include "wa.mm"
include "cc.mm"
include "ffvelrnda.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "expcl.mm"
include "sylan.mm"
include "mulcld.mm"
include "cli.mm"
include "cfz.mm"
include "cvv.mm"
include "serf.mm"
include "ccom.mm"
include "cbl.mm"
include "cdm.mm"
include "cdif.mm"
include "wss.mm"
include "abelthlem2.mm"
include "simprd.mm"
include "sseldd.mm"
include "abelthlem5.mm"
include "mpdan.mm"
include "isumclim2.mm"
include "seqex.mm"
include "a1i.mm"
include "0nn0.mm"
include "sumeq1d.mm"
include "fzfid.mm"
include "wf.mm"
include "adantr.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fsumcl.mm"
include "eqeltrd.mm"
include "cshi.mm"
include "peano2zd.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "nnm1nn0.mm"
include "ax-1cn.mm"
include "nncn.mm"
include "nn0ex.mm"
include "mptex.mm"
include "shftval.mm"
include "sylancr.mm"
include "eqidd.mm"
include "syl6eleq.mm"
include "fsumser.mm"
include "expm1t.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "nnnn0.mm"
include "mul12d.mm"
include "3eqtr4d.mm"
include "sylan2br.mm"
include "seqfeq.mm"
include "isermulc2.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "1z.mm"
include "isershft.mm"
include "mp2an.mm"
include "sylib.mm"
include "eqbrtrrd.mm"
include "clim2ser2.mm"
include "seq1.mm"
include "ax-mp.mm"
include "c0.mm"
include "clt.mm"
include "cr.mm"
include "0re.mm"
include "ltm1.mm"
include "peano2zm.mm"
include "fzn.mm"
include "mpbi.mm"
include "syl6eq.mm"
include "sum0.mm"
include "sylancl.mm"
include "mul02d.mm"
include "syl5eq.mm"
include "isumcl.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "simpr.mm"
include "simpl.mm"
include "fsumm1.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "pncan2d.mm"
include "eqtr2d.mm"
include "subdird.mm"
include "sersub.mm"
include "climsub.mm"
include "1cnd.mm"
include "mulid2d.mm"
include "breqtrrd.mm"
include "isumclim.mm"

theorem abelthlem6
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let cR: class R
  let vr: setvar r
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }
  assume abelth.6: |- F = ( x e. S |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )
  assume abelth.7: |- ( ph -> seq 0 ( + , A ) ~~> 0 )
  assume abelthlem6.1: |- ( ph -> X e. ( S \ { 1 } ) )

  disjoint n x
  disjoint n z
  disjoint M n
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint X n
  disjoint X x
  disjoint X z
  disjoint A n
  disjoint A x
  disjoint A z
  disjoint n ph
  disjoint ph x
  disjoint S n
  disjoint S x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint M j
  disjoint k m
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint M k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n w
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint y z
  disjoint M y
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint X k
  disjoint n r
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint i t
  disjoint i v
  disjoint A i
  disjoint j t
  disjoint j v
  disjoint A j
  disjoint k t
  disjoint k v
  disjoint A k
  disjoint m r
  disjoint m t
  disjoint m v
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint A r
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint F w
  disjoint F y
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S r
  disjoint S w
  disjoint S y
  assert |- ( ph -> ( F ` X ) = ( ( 1 - X ) x. sum_ n e. NN0 ( ( seq 0 ( + , A ) ` n ) x. ( X ^ n ) ) ) )

  proof
    wph
    cX
    cF
    cfv
    #
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    cX
    @1
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    c1
    cX
    cmin
    co
    cn0
    @1
    caddc
    cA
    cc0
    cseq
    #
    cfv
    #
    @3
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    wph
    cX
    cS
    wcel
    @0
    @5
    wceq
    wph
    cX
    cS
    c1
    csn
    #
    abelthlem6.1
    eldifad
    #
    vx
    cX
    cn0
    @2
    vx
    cv
    #
    @1
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    @5
    cS
    cF
    @13
    cX
    wceq
    #
    cn0
    @15
    @4
    vn
    @16
    @14
    @3
    @2
    cmul
    @13
    cX
    @1
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    abelth.6
    cn0
    @4
    vn
    sumex
    fvmpt
    syl
    wph
    @4
    @10
    vn
    vk
    cn0
    vk
    cv
    #
    cA
    cfv
    #
    cX
    @17
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    @1
    cn0
    wcel
    #
    @1
    @21
    cfv
    #
    @4
    wceq
    wph
    vk
    @1
    @20
    @4
    cn0
    @21
    vk
    vn
    weq
    #
    @18
    @2
    @19
    @3
    cmul
    @17
    @1
    cA
    fveq2
    @17
    @1
    cX
    cexp
    oveq2
    #
    oveq12d
    @21
    eqid
    @2
    @3
    cmul
    ovex
    fvmpt
    adantl
    #
    wph
    @23
    wa
    #
    @2
    @3
    wph
    cn0
    cc
    @1
    cA
    abelth.1
    ffvelrnda
    #
    wph
    cX
    cc
    wcel
    #
    @23
    @3
    cc
    wcel
    wph
    cS
    cc
    cX
    cS
    c1
    vz
    cv
    #
    cmin
    co
    cabs
    cfv
    cM
    c1
    @31
    cabs
    cfv
    cmin
    co
    cmul
    co
    cle
    wbr
    #
    vz
    cc
    crab
    cc
    abelth.5
    @32
    vz
    cc
    ssrab2
    eqsstri
    @12
    sseldi
    #
    cX
    @1
    expcl
    sylan
    #
    mulcld
    wph
    caddc
    @21
    cc0
    cseq
    #
    @9
    cX
    @9
    cmul
    co
    #
    cmin
    co
    #
    @10
    cli
    wph
    @9
    @36
    vi
    caddc
    vk
    cn0
    @17
    @6
    cfv
    #
    @19
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    caddc
    vk
    cn0
    cc0
    @17
    c1
    cmin
    co
    #
    cfz
    co
    #
    vm
    cv
    #
    cA
    cfv
    #
    vm
    csu
    #
    @19
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    @35
    cc0
    cvv
    cn0
    nn0uz
    @22
    wph
    @8
    vn
    @40
    cc0
    cn0
    nn0uz
    @22
    @23
    @1
    @40
    cfv
    #
    @8
    wceq
    wph
    vk
    @1
    @39
    @8
    cn0
    @40
    @25
    @38
    @7
    @19
    @3
    cmul
    @17
    @1
    @6
    fveq2
    @26
    oveq12d
    @40
    eqid
    #
    @7
    @3
    cmul
    ovex
    fvmpt
    adantl
    #
    @28
    @7
    @3
    wph
    cn0
    cc
    @1
    @6
    wph
    vn
    cA
    cc0
    cn0
    nn0uz
    @22
    @29
    serf
    #
    ffvelrnda
    #
    @34
    mulcld
    #
    wph
    cX
    cc0
    c1
    cabs
    cmin
    ccom
    cbl
    cfv
    co
    #
    wcel
    @41
    cli
    cdm
    wcel
    wph
    cS
    @11
    cdif
    #
    @56
    cX
    wph
    c1
    cS
    wcel
    @57
    @56
    wss
    wph
    vz
    cA
    cS
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelthlem2
    simprd
    abelthlem6.1
    sseldd
    wph
    vx
    vz
    cA
    cS
    vk
    vn
    cF
    cM
    cX
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelth.7
    abelthlem5
    mpdan
    #
    isumclim2
    #
    @35
    cvv
    wcel
    wph
    caddc
    @21
    cc0
    seqex
    a1i
    wph
    @49
    @36
    cc0
    @49
    cfv
    #
    caddc
    co
    #
    @36
    cli
    wph
    @36
    vi
    @48
    cc0
    cc0
    cn0
    nn0uz
    cc0
    cn0
    wcel
    #
    wph
    0nn0
    a1i
    wph
    vi
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @63
    @48
    cfv
    #
    cc0
    @63
    c1
    cmin
    co
    #
    cfz
    co
    #
    @45
    vm
    csu
    #
    cX
    @63
    cexp
    co
    #
    cmul
    co
    #
    cc
    @64
    @66
    @71
    wceq
    wph
    vk
    @63
    @47
    @71
    cn0
    @48
    vk
    vi
    weq
    #
    @46
    @69
    @19
    @70
    cmul
    @72
    @43
    @68
    @45
    vm
    @72
    @42
    @67
    cc0
    cfz
    @17
    @63
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    @17
    @63
    cX
    cexp
    oveq2
    #
    oveq12d
    @48
    eqid
    #
    @69
    @70
    cmul
    ovex
    fvmpt
    adantl
    @65
    @69
    @70
    @65
    @68
    @45
    vm
    @65
    cc0
    @67
    fzfid
    @65
    cn0
    cc
    cA
    wf
    #
    @44
    cn0
    wcel
    #
    @45
    cc
    wcel
    #
    @44
    @68
    wcel
    wph
    @75
    @64
    abelth.1
    adantr
    @44
    @67
    elfznn0
    cn0
    cc
    @44
    cA
    ffvelrn
    #
    syl2an
    fsumcl
    wph
    @30
    @64
    @70
    cc
    wcel
    @33
    cX
    @63
    expcl
    sylan
    #
    mulcld
    eqeltrd
    #
    wph
    caddc
    vk
    cn0
    cX
    @39
    cmul
    co
    #
    cmpt
    #
    c1
    cshi
    co
    #
    cc0
    c1
    caddc
    co
    #
    cseq
    #
    caddc
    @48
    @84
    cseq
    @36
    cli
    wph
    caddc
    vn
    @83
    @48
    @84
    wph
    cc0
    @22
    peano2zd
    @1
    @84
    cuz
    cfv
    #
    wcel
    wph
    @1
    cn
    wcel
    #
    @1
    @83
    cfv
    #
    @1
    @48
    cfv
    #
    wceq
    cn
    @86
    @1
    cn
    c1
    cuz
    cfv
    @86
    nnuz
    c1
    @84
    cuz
    1e0p1
    fveq2i
    eqtri
    eleq2i
    wph
    @87
    wa
    #
    @1
    c1
    cmin
    co
    #
    @82
    cfv
    #
    cX
    @91
    @6
    cfv
    #
    cX
    @91
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @88
    @89
    @90
    @91
    cn0
    wcel
    #
    @92
    @96
    wceq
    @87
    @97
    wph
    @1
    nnm1nn0
    #
    adantl
    #
    vk
    @91
    @81
    @96
    cn0
    @82
    @17
    @91
    wceq
    #
    @39
    @95
    cX
    cmul
    @100
    @38
    @93
    @19
    @94
    cmul
    @17
    @91
    @6
    fveq2
    @17
    @91
    cX
    cexp
    oveq2
    oveq12d
    oveq2d
    @82
    eqid
    #
    cX
    @95
    cmul
    ovex
    fvmpt
    syl
    @90
    c1
    cc
    wcel
    @1
    cc
    wcel
    #
    @88
    @92
    wceq
    ax-1cn
    @87
    @102
    wph
    @1
    nncn
    adantl
    c1
    @1
    @82
    vk
    cn0
    @81
    nn0ex
    mptex
    #
    shftval
    sylancr
    @90
    cc0
    @91
    cfz
    co
    #
    @45
    vm
    csu
    #
    @3
    cmul
    co
    #
    @93
    cX
    @94
    cmul
    co
    #
    cmul
    co
    @89
    @96
    @90
    @105
    @93
    @3
    @107
    cmul
    @90
    @45
    vm
    cA
    cc0
    @91
    @90
    @44
    @104
    wcel
    #
    wa
    @45
    eqidd
    @90
    @91
    cn0
    cc0
    cuz
    cfv
    #
    @99
    nn0uz
    syl6eleq
    @90
    @75
    @76
    @77
    @108
    wph
    @75
    @87
    abelth.1
    adantr
    @44
    @91
    elfznn0
    #
    @78
    syl2an
    fsumser
    @90
    @3
    @94
    cX
    cmul
    co
    #
    @107
    wph
    @30
    @87
    @3
    @111
    wceq
    @33
    cX
    @1
    expm1t
    sylan
    @90
    cX
    @94
    wph
    @30
    @87
    @33
    adantr
    #
    wph
    @30
    @97
    @94
    cc
    wcel
    @87
    @33
    @98
    cX
    @91
    expcl
    syl2an
    #
    mulcomd
    eqtr4d
    oveq12d
    @90
    @23
    @89
    @106
    wceq
    #
    @87
    @23
    wph
    @1
    nnnn0
    adantl
    vk
    @1
    @47
    @106
    cn0
    @48
    @25
    @46
    @105
    @19
    @3
    cmul
    @25
    @43
    @104
    @45
    vm
    @25
    @42
    @91
    cc0
    cfz
    @17
    @1
    c1
    cmin
    oveq1
    oveq2d
    sumeq1d
    @26
    oveq12d
    @74
    @105
    @3
    cmul
    ovex
    fvmpt
    #
    syl
    @90
    cX
    @93
    @94
    @112
    wph
    cn0
    cc
    @6
    wf
    @97
    @93
    cc
    wcel
    @87
    @53
    @98
    cn0
    cc
    @91
    @6
    ffvelrn
    syl2an
    @113
    mul12d
    3eqtr4d
    3eqtr4d
    sylan2br
    seqfeq
    wph
    caddc
    @82
    cc0
    cseq
    @36
    cli
    wbr
    #
    @85
    @36
    cli
    wbr
    #
    wph
    @9
    cX
    vi
    @40
    @82
    cc0
    cn0
    nn0uz
    @22
    @33
    @59
    @65
    @63
    @40
    cfv
    #
    @63
    @6
    cfv
    #
    @70
    cmul
    co
    #
    cc
    @64
    @118
    @120
    wceq
    wph
    vk
    @63
    @39
    @120
    cn0
    @40
    @72
    @38
    @119
    @19
    @70
    cmul
    @17
    @63
    @6
    fveq2
    @73
    oveq12d
    #
    @51
    @119
    @70
    cmul
    ovex
    fvmpt
    adantl
    #
    @65
    @119
    @70
    wph
    cn0
    cc
    @63
    @6
    @53
    ffvelrnda
    @79
    mulcld
    eqeltrd
    #
    @65
    @63
    @82
    cfv
    #
    cX
    @120
    cmul
    co
    #
    cX
    @118
    cmul
    co
    @64
    @124
    @125
    wceq
    wph
    vk
    @63
    @81
    @125
    cn0
    @82
    @72
    @39
    @120
    cX
    cmul
    @121
    oveq2d
    @101
    cX
    @120
    cmul
    ovex
    fvmpt
    adantl
    @65
    @118
    @120
    cX
    cmul
    @122
    oveq2d
    eqtr4d
    isermulc2
    cc0
    cz
    wcel
    #
    c1
    cz
    wcel
    @116
    @117
    wb
    0z
    1z
    @36
    caddc
    @82
    cc0
    c1
    @103
    isershft
    mp2an
    sylib
    eqbrtrrd
    clim2ser2
    wph
    @61
    @36
    cc0
    caddc
    co
    @36
    wph
    @60
    cc0
    @36
    caddc
    wph
    @60
    cc0
    cX
    cc0
    cexp
    co
    #
    cmul
    co
    #
    cc0
    @60
    cc0
    @48
    cfv
    #
    @128
    @126
    @60
    @129
    wceq
    0z
    caddc
    @48
    cc0
    seq1
    ax-mp
    @62
    @129
    @128
    wceq
    0nn0
    vk
    cc0
    @47
    @128
    cn0
    @48
    @17
    cc0
    wceq
    #
    @46
    cc0
    @19
    @127
    cmul
    @130
    @46
    c0
    @45
    vm
    csu
    cc0
    @130
    @43
    c0
    @45
    vm
    @130
    @43
    cc0
    cc0
    c1
    cmin
    co
    #
    cfz
    co
    #
    c0
    @130
    @42
    @131
    cc0
    cfz
    @17
    cc0
    c1
    cmin
    oveq1
    oveq2d
    @131
    cc0
    clt
    wbr
    #
    @132
    c0
    wceq
    #
    cc0
    cr
    wcel
    @133
    0re
    cc0
    ltm1
    ax-mp
    @126
    @131
    cz
    wcel
    #
    @133
    @134
    wb
    0z
    @126
    @135
    0z
    cc0
    peano2zm
    ax-mp
    cc0
    @131
    fzn
    mp2an
    mpbi
    syl6eq
    sumeq1d
    @45
    vm
    sum0
    syl6eq
    @17
    cc0
    cX
    cexp
    oveq2
    oveq12d
    @74
    cc0
    @127
    cmul
    ovex
    fvmpt
    ax-mp
    eqtri
    wph
    @127
    wph
    @30
    @62
    @127
    cc
    wcel
    @33
    0nn0
    cX
    cc0
    expcl
    sylancl
    mul02d
    syl5eq
    oveq2d
    wph
    @36
    wph
    cX
    @9
    @33
    wph
    @8
    vn
    @40
    cc0
    cn0
    nn0uz
    @22
    @52
    @55
    @58
    isumcl
    #
    mulcld
    addid1d
    eqtrd
    breqtrd
    wph
    cn0
    cc
    @63
    @41
    wph
    vi
    @40
    cc0
    cn0
    nn0uz
    @22
    @123
    serf
    ffvelrnda
    wph
    cn0
    cc
    @63
    @49
    wph
    vi
    @48
    cc0
    cn0
    nn0uz
    @22
    @80
    serf
    ffvelrnda
    @65
    vn
    @40
    @48
    @21
    cc0
    @63
    @65
    @63
    cn0
    @109
    wph
    @64
    simpr
    nn0uz
    syl6eleq
    @65
    wph
    @23
    @50
    cc
    wcel
    @1
    cc0
    @63
    cfz
    co
    wcel
    #
    wph
    @64
    simpl
    #
    @1
    @63
    elfznn0
    #
    @28
    @50
    @8
    cc
    @52
    @55
    eqeltrd
    syl2an
    @65
    wph
    @23
    @89
    cc
    wcel
    @137
    @138
    @139
    @28
    @89
    @106
    cc
    @23
    @114
    wph
    @115
    adantl
    #
    @28
    @105
    @3
    @28
    @104
    @45
    vm
    @28
    cc0
    @91
    fzfid
    @28
    @75
    @76
    @77
    @108
    wph
    @75
    @23
    abelth.1
    adantr
    #
    @110
    @78
    syl2an
    fsumcl
    #
    @34
    mulcld
    eqeltrd
    syl2an
    @65
    wph
    @23
    @24
    @50
    @89
    cmin
    co
    #
    wceq
    @137
    @138
    @139
    @28
    @4
    @8
    @106
    cmin
    co
    #
    @24
    @143
    @28
    @4
    @7
    @105
    cmin
    co
    #
    @3
    cmul
    co
    @144
    @28
    @2
    @145
    @3
    cmul
    @28
    @145
    @105
    @2
    caddc
    co
    #
    @105
    cmin
    co
    @2
    @28
    @7
    @146
    @105
    cmin
    @28
    cc0
    @1
    cfz
    co
    #
    @45
    vm
    csu
    @7
    @146
    @28
    @45
    vm
    cA
    cc0
    @1
    @28
    @44
    @147
    wcel
    #
    wa
    @45
    eqidd
    @28
    @1
    cn0
    @109
    wph
    @23
    simpr
    nn0uz
    syl6eleq
    #
    @28
    @75
    @76
    @77
    @148
    @141
    @44
    @1
    elfznn0
    @78
    syl2an
    #
    fsumser
    @28
    @45
    @2
    vm
    cc0
    @1
    @149
    @150
    @44
    @1
    cA
    fveq2
    fsumm1
    eqtr3d
    oveq1d
    @28
    @105
    @2
    @142
    @29
    pncan2d
    eqtr2d
    oveq1d
    @28
    @7
    @105
    @3
    @54
    @142
    @34
    subdird
    eqtrd
    @27
    @28
    @50
    @8
    @89
    @106
    cmin
    @52
    @140
    oveq12d
    3eqtr4d
    syl2an
    sersub
    climsub
    wph
    @10
    c1
    @9
    cmul
    co
    #
    @36
    cmin
    co
    @37
    wph
    c1
    cX
    @9
    wph
    1cnd
    @33
    @136
    subdird
    wph
    @151
    @9
    @36
    cmin
    wph
    @9
    @136
    mulid2d
    oveq1d
    eqtrd
    breqtrrd
    isumclim
    eqtrd
end
