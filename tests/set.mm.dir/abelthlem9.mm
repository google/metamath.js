include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "cc0.mm"
include "wceq.mm"
include "csu.mm"
include "cif.mm"
include "cmpt.mm"
include "cexp.mm"
include "cmul.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cc.mm"
include "wf.mm"
include "0nn0.mm"
include "a1i.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "nn0uz.mm"
include "0zd.mm"
include "eqidd.mm"
include "ffvelrnda.mm"
include "isumcl.mm"
include "adantr.mm"
include "subcld.mm"
include "ifcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cz.mm"
include "1e0p1.mm"
include "1z.mm"
include "eqeltrri.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "nnnn0.mm"
include "adantl.mm"
include "weq.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "ovex.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "wne.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "sylan2br.mm"
include "seqfeq.mm"
include "isumclim2.mm"
include "clim2ser.mm"
include "0z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "syl6breq.mm"
include "eqbrtrd.mm"
include "clim2ser2.mm"
include "iftrue.mm"
include "sylancl.mm"
include "npncan2.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "breqtrd.mm"
include "seqex.mm"
include "c0ex.mm"
include "breldm.mm"
include "abelthlem8.mm"
include "wb.mm"
include "csn.mm"
include "cdif.mm"
include "ccom.mm"
include "cbl.mm"
include "wss.mm"
include "abelthlem2.mm"
include "simpld.mm"
include "oveq1.mm"
include "nn0z.mm"
include "1exp.mm"
include "sylan9eq.mm"
include "oveq12d.mm"
include "sumeq2dv.mm"
include "sumex.mm"
include "ad2antrr.mm"
include "adantlr.mm"
include "mulid1d.mm"
include "eqtr4d.mm"
include "eqeltrd.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cbvsumv.mm"
include "syl6eq.mm"
include "subidd.mm"
include "breqtrrd.mm"
include "isumclim.mm"
include "oveqan12rd.mm"
include "oveq2.mm"
include "cle.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sselda.mm"
include "expcl.mm"
include "sylan.mm"
include "mulcld.mm"
include "3eqtr4d.mm"
include "abelthlem3.mm"
include "sumeq2sdv.mm"
include "exp0d.mm"
include "abelthlem4.mm"
include "npncand.mm"
include "ffvelrnd.mm"
include "nnncan2d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "mpbid.mm"

theorem abelthlem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vr: setvar r
  let cX: class X
  let vt: setvar t
  let vv: setvar v
  let cN: class N
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }
  assume abelth.6: |- F = ( x e. S |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )

  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint M n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint x z
  disjoint M x
  disjoint y z
  disjoint M y
  disjoint M z
  disjoint R n
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint A n
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint F w
  disjoint F y
  disjoint S n
  disjoint S w
  disjoint S x
  disjoint S y
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
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint X k
  disjoint n r
  disjoint X n
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint X x
  disjoint X z
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
  disjoint N k
  disjoint N n
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint S m
  disjoint S r
  assert |- ( ( ph /\ R e. RR+ ) -> E. w e. RR+ A. y e. S ( ( abs ` ( 1 - y ) ) < w -> ( abs ` ( ( F ` 1 ) - ( F ` y ) ) ) < R ) )

  proof
    wph
    cR
    crp
    wcel
    #
    wa
    c1
    vy
    cv
    #
    cmin
    co
    cabs
    cfv
    vw
    cv
    clt
    wbr
    #
    c1
    vx
    cS
    cn0
    vi
    cv
    #
    vk
    cn0
    vk
    cv
    #
    cc0
    wceq
    #
    cc0
    cA
    cfv
    #
    cn0
    vm
    cv
    #
    cA
    cfv
    #
    vm
    csu
    #
    cmin
    co
    #
    @4
    cA
    cfv
    #
    cif
    #
    cmpt
    #
    cfv
    #
    vx
    cv
    #
    @3
    cexp
    co
    #
    cmul
    co
    #
    vi
    csu
    #
    cmpt
    #
    cfv
    #
    @1
    @19
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    #
    vw
    crp
    wrex
    #
    @2
    c1
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    #
    vw
    crp
    wrex
    #
    wph
    vx
    vy
    vz
    vw
    @13
    cR
    cS
    vi
    @19
    cM
    wph
    vk
    cn0
    @12
    cc
    @13
    wph
    @4
    cn0
    wcel
    #
    wa
    #
    @5
    @10
    @11
    cc
    @37
    @6
    @9
    wph
    cn0
    cc
    cA
    wf
    #
    cc0
    cn0
    wcel
    #
    @6
    cc
    wcel
    #
    @36
    abelth.1
    @39
    @36
    0nn0
    a1i
    cn0
    cc
    cc0
    cA
    ffvelrn
    #
    syl2an
    wph
    @9
    cc
    wcel
    #
    @36
    wph
    @8
    vm
    cA
    cc0
    cn0
    nn0uz
    wph
    0zd
    #
    wph
    @7
    cn0
    wcel
    wa
    #
    @8
    eqidd
    #
    wph
    cn0
    cc
    @7
    cA
    abelth.1
    ffvelrnda
    #
    abelth.2
    isumcl
    #
    adantr
    subcld
    wph
    cn0
    cc
    @4
    cA
    abelth.1
    ffvelrnda
    #
    ifcld
    #
    @13
    eqid
    #
    fmptd
    #
    wph
    caddc
    @13
    cc0
    cseq
    #
    cc0
    cli
    wbr
    @52
    cli
    cdm
    wcel
    wph
    @52
    @9
    @6
    cmin
    co
    #
    cc0
    @52
    cfv
    #
    caddc
    co
    #
    cc0
    cli
    wph
    @53
    vi
    @13
    cc0
    cc0
    cn0
    nn0uz
    @39
    wph
    0nn0
    a1i
    #
    wph
    cn0
    cc
    @3
    @13
    @51
    ffvelrnda
    wph
    caddc
    @13
    cc0
    c1
    caddc
    co
    #
    cseq
    caddc
    cA
    @57
    cseq
    #
    @53
    cli
    wph
    caddc
    vi
    @13
    cA
    @57
    @57
    cz
    wcel
    wph
    c1
    @57
    cz
    1e0p1
    1z
    eqeltrri
    a1i
    #
    @3
    @57
    cuz
    cfv
    #
    wcel
    #
    wph
    @3
    cn
    wcel
    #
    @14
    @3
    cA
    cfv
    #
    wceq
    cn
    @60
    @3
    cn
    c1
    cuz
    cfv
    @60
    nnuz
    c1
    @57
    cuz
    1e0p1
    fveq2i
    eqtri
    eleq2i
    #
    wph
    @62
    wa
    #
    @14
    @3
    cc0
    wceq
    #
    @10
    @63
    cif
    #
    @63
    @65
    @3
    cn0
    wcel
    #
    @14
    @67
    wceq
    #
    @62
    @68
    wph
    @3
    nnnn0
    adantl
    #
    vk
    @3
    @12
    @67
    cn0
    @13
    vk
    vi
    weq
    #
    @5
    @66
    @11
    @63
    @10
    @4
    @3
    cc0
    eqeq1
    @4
    @3
    cA
    fveq2
    #
    ifbieq2d
    #
    @50
    @66
    @10
    @63
    @6
    @9
    cmin
    ovex
    #
    @3
    cA
    fvex
    ifex
    fvmpt
    #
    syl
    @65
    @66
    @10
    @63
    @65
    @3
    cc0
    @62
    @3
    cc0
    wne
    wph
    @3
    nnne0
    adantl
    neneqd
    iffalsed
    #
    eqtrd
    sylan2br
    seqfeq
    wph
    @58
    @9
    cc0
    caddc
    cA
    cc0
    cseq
    cfv
    #
    cmin
    co
    @53
    cli
    wph
    @9
    vk
    cA
    cc0
    cc0
    cn0
    nn0uz
    @56
    @48
    wph
    @8
    vm
    cA
    cc0
    cn0
    nn0uz
    @43
    @45
    @46
    abelth.2
    isumclim2
    clim2ser
    @77
    @6
    @9
    cmin
    cc0
    cz
    wcel
    #
    @77
    @6
    wceq
    0z
    caddc
    cA
    cc0
    seq1
    ax-mp
    oveq2i
    syl6breq
    eqbrtrd
    clim2ser2
    wph
    @55
    @53
    @10
    caddc
    co
    #
    cc0
    @54
    @10
    @53
    caddc
    @54
    cc0
    @13
    cfv
    #
    @10
    @78
    @54
    @80
    wceq
    0z
    caddc
    @13
    cc0
    seq1
    ax-mp
    @39
    @80
    @10
    wceq
    0nn0
    vk
    cc0
    @12
    @10
    cn0
    @13
    @5
    @10
    @11
    iftrue
    #
    @50
    @74
    fvmpt
    ax-mp
    eqtri
    oveq2i
    wph
    @42
    @40
    @79
    cc0
    wceq
    @47
    wph
    @38
    @39
    @40
    abelth.1
    0nn0
    @41
    sylancl
    #
    @9
    @6
    npncan2
    syl2anc
    syl5eq
    breqtrd
    #
    @52
    cc0
    cli
    caddc
    @13
    cc0
    seqex
    c0ex
    breldm
    syl
    abelth.3
    abelth.4
    abelth.5
    @19
    eqid
    #
    @83
    abelthlem8
    wph
    @27
    @35
    wb
    @0
    wph
    @26
    @34
    vw
    crp
    wph
    @25
    @33
    vy
    cS
    wph
    @1
    cS
    wcel
    #
    wa
    #
    @24
    @32
    @2
    @86
    @23
    @31
    cR
    clt
    @86
    @22
    @30
    cabs
    @86
    @22
    @28
    @9
    cmin
    co
    #
    @29
    @9
    cmin
    co
    #
    cmin
    co
    @30
    @86
    @20
    @87
    @21
    @88
    cmin
    @86
    @20
    cn0
    @67
    c1
    cmul
    co
    #
    vi
    csu
    #
    @87
    @86
    c1
    cS
    wcel
    #
    @20
    @90
    wceq
    wph
    @91
    @85
    wph
    @91
    cS
    c1
    csn
    cdif
    cc0
    c1
    cabs
    cmin
    ccom
    cbl
    cfv
    co
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
    simpld
    #
    adantr
    #
    vx
    c1
    @18
    @90
    cS
    @19
    @15
    c1
    wceq
    #
    cn0
    @17
    @89
    vi
    @94
    @68
    wa
    @14
    @67
    @16
    c1
    cmul
    @68
    @69
    @94
    @75
    adantl
    @94
    @68
    @16
    c1
    @3
    cexp
    co
    #
    c1
    @15
    c1
    @3
    cexp
    oveq1
    @68
    @3
    cz
    wcel
    @95
    c1
    wceq
    @3
    nn0z
    @3
    1exp
    syl
    sylan9eq
    oveq12d
    sumeq2dv
    @84
    cn0
    @89
    vi
    sumex
    fvmpt
    syl
    @86
    @89
    @87
    vi
    @13
    cc0
    cn0
    nn0uz
    @86
    0zd
    #
    @86
    @68
    wa
    #
    @14
    @67
    @89
    @68
    @69
    @86
    @75
    adantl
    @97
    @67
    @97
    @66
    @10
    @63
    cc
    wph
    @10
    cc
    wcel
    @85
    @68
    wph
    @6
    @9
    @82
    @47
    subcld
    ad2antrr
    wph
    @68
    @63
    cc
    wcel
    @85
    wph
    cn0
    cc
    @3
    cA
    abelth.1
    ffvelrnda
    adantlr
    #
    ifcld
    #
    mulid1d
    #
    eqtr4d
    @97
    @89
    @67
    cc
    @100
    @99
    eqeltrd
    wph
    @52
    @87
    cli
    wbr
    @85
    wph
    @52
    cc0
    @87
    cli
    @83
    wph
    @87
    @9
    @9
    cmin
    co
    cc0
    wph
    @28
    @9
    @9
    cmin
    wph
    @28
    cn0
    @8
    c1
    cmul
    co
    #
    vm
    csu
    #
    @9
    wph
    @91
    @28
    @102
    wceq
    @92
    vx
    c1
    cn0
    vn
    cv
    #
    cA
    cfv
    #
    @15
    @103
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    @102
    cS
    cF
    @94
    @107
    cn0
    @104
    c1
    cmul
    co
    #
    vn
    csu
    @102
    @94
    cn0
    @106
    @108
    vn
    @94
    @103
    cn0
    wcel
    #
    wa
    @105
    c1
    @104
    cmul
    @94
    @109
    @105
    c1
    @103
    cexp
    co
    #
    c1
    @15
    c1
    @103
    cexp
    oveq1
    @109
    @103
    cz
    wcel
    @110
    c1
    wceq
    @103
    nn0z
    @103
    1exp
    syl
    sylan9eq
    oveq2d
    sumeq2dv
    cn0
    @108
    @101
    vn
    vm
    vn
    vm
    weq
    @104
    @8
    c1
    cmul
    @103
    @7
    cA
    fveq2
    oveq1d
    cbvsumv
    syl6eq
    abelth.6
    cn0
    @101
    vm
    sumex
    fvmpt
    syl
    wph
    cn0
    @101
    @8
    vm
    @44
    @8
    @46
    mulid1d
    sumeq2dv
    eqtrd
    oveq1d
    wph
    @9
    @47
    subidd
    eqtrd
    breqtrrd
    adantr
    isumclim
    eqtrd
    @86
    @21
    cn0
    @67
    @1
    @3
    cexp
    co
    #
    cmul
    co
    #
    vi
    csu
    #
    @88
    @85
    @21
    @113
    wceq
    wph
    vx
    @1
    @18
    @113
    cS
    @19
    vx
    vy
    weq
    #
    cn0
    @17
    @112
    vi
    @68
    @114
    @14
    @67
    @16
    @111
    cmul
    @75
    @15
    @1
    @3
    cexp
    oveq1
    #
    oveqan12rd
    sumeq2dv
    @84
    cn0
    @112
    vi
    sumex
    fvmpt
    adantl
    @86
    @112
    @88
    vi
    vk
    cn0
    @12
    @1
    @4
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
    @96
    @68
    @3
    @118
    cfv
    #
    @112
    wceq
    #
    @86
    vk
    @3
    @117
    @112
    cn0
    @118
    @71
    @12
    @67
    @116
    @111
    cmul
    @73
    @4
    @3
    @1
    cexp
    oveq2
    #
    oveq12d
    @118
    eqid
    #
    @67
    @111
    cmul
    ovex
    fvmpt
    #
    adantl
    @97
    @67
    @111
    @99
    @86
    @1
    cc
    wcel
    #
    @68
    @111
    cc
    wcel
    wph
    cS
    cc
    @1
    cS
    cc
    wss
    wph
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
    @125
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
    @126
    vz
    cc
    ssrab2
    eqsstri
    a1i
    sselda
    #
    @1
    @3
    expcl
    sylan
    #
    mulcld
    @86
    caddc
    @118
    cc0
    cseq
    #
    @29
    @6
    cmin
    co
    #
    cc0
    @129
    cfv
    #
    caddc
    co
    #
    @88
    cli
    @86
    @130
    vi
    @118
    cc0
    cc0
    cn0
    nn0uz
    @39
    @86
    0nn0
    a1i
    #
    @86
    cn0
    cc
    @3
    @118
    @86
    vk
    cn0
    @117
    cc
    @118
    @86
    @36
    wa
    #
    @12
    @116
    wph
    @36
    @12
    cc
    wcel
    @85
    @49
    adantlr
    @86
    @124
    @36
    @116
    cc
    wcel
    @127
    @1
    @4
    expcl
    sylan
    #
    mulcld
    @122
    fmptd
    ffvelrnda
    @86
    caddc
    @118
    @57
    cseq
    #
    caddc
    vk
    cn0
    @11
    @116
    cmul
    co
    #
    cmpt
    #
    @57
    cseq
    #
    @130
    cli
    wph
    @136
    @139
    wceq
    @85
    wph
    caddc
    vi
    @118
    @138
    @57
    @59
    @61
    wph
    @62
    @119
    @3
    @138
    cfv
    #
    wceq
    @64
    @65
    @112
    @63
    @111
    cmul
    co
    #
    @119
    @140
    @65
    @67
    @63
    @111
    cmul
    @76
    oveq1d
    @65
    @68
    @120
    @70
    @123
    syl
    @65
    @68
    @140
    @141
    wceq
    #
    @70
    vk
    @3
    @137
    @141
    cn0
    @138
    @71
    @11
    @63
    @116
    @111
    cmul
    @72
    @121
    oveq12d
    @138
    eqid
    #
    @63
    @111
    cmul
    ovex
    fvmpt
    #
    syl
    3eqtr4d
    sylan2br
    seqfeq
    adantr
    @86
    @139
    @29
    cc0
    caddc
    @138
    cc0
    cseq
    #
    cfv
    #
    cmin
    co
    @130
    cli
    @86
    @29
    vi
    @138
    cc0
    cc0
    cn0
    nn0uz
    @133
    @86
    cn0
    cc
    @3
    @138
    @86
    vk
    cn0
    @137
    cc
    @138
    @134
    @11
    @116
    wph
    @36
    @11
    cc
    wcel
    @85
    @48
    adantlr
    @135
    mulcld
    @143
    fmptd
    ffvelrnda
    @86
    @145
    cn0
    @141
    vi
    csu
    #
    @29
    cli
    @86
    @141
    vi
    @138
    cc0
    cn0
    nn0uz
    @96
    @68
    @142
    @86
    @144
    adantl
    @97
    @63
    @111
    @98
    @128
    mulcld
    wph
    vz
    cA
    cS
    vk
    cM
    @1
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelthlem3
    isumclim2
    @85
    @29
    @147
    wceq
    wph
    vx
    @1
    @107
    @147
    cS
    cF
    @114
    @107
    cn0
    @63
    @16
    cmul
    co
    #
    vi
    csu
    @147
    cn0
    @106
    @148
    vn
    vi
    vn
    vi
    weq
    @104
    @63
    @105
    @16
    cmul
    @103
    @3
    cA
    fveq2
    @103
    @3
    @15
    cexp
    oveq2
    oveq12d
    cbvsumv
    @114
    cn0
    @148
    @141
    vi
    @114
    @16
    @111
    @63
    cmul
    @115
    oveq2d
    sumeq2sdv
    syl5eq
    abelth.6
    cn0
    @141
    vi
    sumex
    fvmpt
    adantl
    breqtrrd
    clim2ser
    @86
    @146
    @6
    @29
    cmin
    @86
    @146
    @6
    @1
    cc0
    cexp
    co
    #
    cmul
    co
    #
    @6
    @146
    cc0
    @138
    cfv
    #
    @150
    @78
    @146
    @151
    wceq
    0z
    caddc
    @138
    cc0
    seq1
    ax-mp
    @39
    @151
    @150
    wceq
    0nn0
    vk
    cc0
    @137
    @150
    cn0
    @138
    @5
    @11
    @6
    @116
    @149
    cmul
    @4
    cc0
    cA
    fveq2
    @4
    cc0
    @1
    cexp
    oveq2
    #
    oveq12d
    @143
    @6
    @149
    cmul
    ovex
    fvmpt
    ax-mp
    eqtri
    @86
    @150
    @6
    c1
    cmul
    co
    @6
    @86
    @149
    c1
    @6
    cmul
    @86
    @1
    @127
    exp0d
    #
    oveq2d
    @86
    @6
    wph
    @40
    @85
    @82
    adantr
    #
    mulid1d
    eqtrd
    syl5eq
    oveq2d
    breqtrd
    eqbrtrd
    clim2ser2
    @86
    @132
    @130
    @10
    caddc
    co
    @88
    @86
    @131
    @10
    @130
    caddc
    @86
    @131
    @10
    @149
    cmul
    co
    #
    @10
    @131
    cc0
    @118
    cfv
    #
    @155
    @78
    @131
    @156
    wceq
    0z
    caddc
    @118
    cc0
    seq1
    ax-mp
    @39
    @156
    @155
    wceq
    0nn0
    vk
    cc0
    @117
    @155
    cn0
    @118
    @5
    @12
    @10
    @116
    @149
    cmul
    @81
    @152
    oveq12d
    @122
    @10
    @149
    cmul
    ovex
    fvmpt
    ax-mp
    eqtri
    @86
    @155
    @10
    c1
    cmul
    co
    @10
    @86
    @149
    c1
    @10
    cmul
    @153
    oveq2d
    @86
    @10
    @86
    @6
    @9
    @154
    wph
    @42
    @85
    @47
    adantr
    #
    subcld
    mulid1d
    eqtrd
    syl5eq
    oveq2d
    @86
    @29
    @6
    @9
    wph
    cS
    cc
    @1
    cF
    wph
    vx
    vz
    cA
    cS
    vn
    cF
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelthlem4
    #
    ffvelrnda
    #
    @154
    @157
    npncand
    eqtrd
    breqtrd
    isumclim
    eqtrd
    oveq12d
    @86
    @28
    @29
    @9
    @86
    cS
    cc
    c1
    cF
    wph
    cS
    cc
    cF
    wf
    @85
    @158
    adantr
    @93
    ffvelrnd
    @159
    @157
    nnncan2d
    eqtrd
    fveq2d
    breq1d
    imbi2d
    ralbidva
    rexbidv
    adantr
    mpbid
end
