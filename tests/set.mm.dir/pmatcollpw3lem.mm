include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cdecpmat.mm"
include "cdm.mm"
include "cco1.mm"
include "cmpt2.mm"
include "ccur.mm"
include "cmap.mm"
include "csb.mm"
include "cvv.mm"
include "weq.mm"
include "dmeq.mm"
include "dmeqd.mm"
include "oveq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "mpt2eq123dv.mm"
include "fveq2.mm"
include "mpt2eq3dv.mm"
include "cbvmpt2v.mm"
include "dmexg.mm"
include "syl.mm"
include "jca.mm"
include "ad2antrl.mm"
include "mpt2exga.mm"
include "ralrimivva.mm"
include "simprr.mm"
include "nn0ex.mm"
include "ssex.mm"
include "simp3.mm"
include "adantr.mm"
include "mpt2curryvald.mm"
include "csbeq2dv.mm"
include "eqcom.mm"
include "3imtr3i.mm"
include "cbvcsbv.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "adantl.mm"
include "csbied.mm"
include "cbs.mm"
include "cxp.mm"
include "wf.mm"
include "eqid.mm"
include "matbas2i.mm"
include "elmapi.mm"
include "fdm.mm"
include "dmxpid.mm"
include "syl6req.mm"
include "3syl.mm"
include "3ad2ant3.mm"
include "simpr.mm"
include "oveqd.mm"
include "eqtr4d.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "ad2antrr.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "matecld.mm"
include "wi.mm"
include "ssel.mm"
include "imp.mm"
include "coe1fvalcl.mm"
include "syl2anc.mm"
include "matbas2d.mm"
include "eqeltrd.mm"
include "fmptd.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "elmapg.mm"
include "syl2an.mm"
include "mpbird.mm"
include "cres.mm"
include "fveq1.mm"
include "fvmpt2curryd.mm"
include "df-decpmat.mm"
include "reseq1i.mm"
include "ssv.mm"
include "simpl.mm"
include "anim12i.mm"
include "resmpt2.mm"
include "syl5req.mm"
include "adantlr.mm"
include "ovres.mm"
include "sylan.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "eqeq2d.mm"
include "rspcedv.mm"

theorem pmatcollpw3lem
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vn: setvar n
  let c.ex: class .^
  let cI: class I
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  assume pmatcollpw.p: |- P = ( Poly1 ` R )
  assume pmatcollpw.c: |- C = ( N Mat P )
  assume pmatcollpw.b: |- B = ( Base ` C )
  assume pmatcollpw.m: |- .* = ( .s ` C )
  assume pmatcollpw.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpw.x: |- X = ( var1 ` R )
  assume pmatcollpw.t: |- T = ( N matToPolyMat R )
  assume pmatcollpw3.a: |- A = ( N Mat R )
  assume pmatcollpw3.d: |- D = ( Base ` A )

  disjoint B n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint X n
  disjoint .^ n
  disjoint C n
  disjoint B f
  disjoint C f
  disjoint f n
  disjoint D f
  disjoint I f
  disjoint I n
  disjoint M f
  disjoint N f
  disjoint R f
  disjoint T f
  disjoint X f
  disjoint .^ f
  disjoint .* f
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i n
  disjoint j n
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint a n
  disjoint b n
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint P a
  disjoint P b
  disjoint R a
  disjoint R b
  disjoint T a
  disjoint T b
  disjoint X a
  disjoint X b
  disjoint X i
  disjoint X j
  disjoint .* a
  disjoint .* b
  disjoint .^ a
  disjoint .^ b
  disjoint .^ i
  disjoint .^ j
  disjoint B s
  disjoint n s
  disjoint M s
  disjoint N s
  disjoint R s
  disjoint f i
  disjoint f j
  disjoint B k
  disjoint B l
  disjoint B x
  disjoint B y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B m
  disjoint f x
  disjoint n x
  disjoint D k
  disjoint f k
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I x
  disjoint I y
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j x
  disjoint j y
  disjoint k n
  disjoint M k
  disjoint M l
  disjoint M x
  disjoint M y
  disjoint M m
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint N k
  disjoint N l
  disjoint N x
  disjoint N y
  disjoint N m
  disjoint R k
  disjoint R l
  disjoint R x
  disjoint R y
  disjoint R m
  assert |- ( ( ( N e. Fin /\ R e. CRing /\ M e. B ) /\ ( I C_ NN0 /\ I =/= (/) ) ) -> ( M = ( C gsum ( n e. I |-> ( ( n .^ X ) .* ( T ` ( M decompPMat n ) ) ) ) ) -> E. f e. ( D ^m I ) M = ( C gsum ( n e. I |-> ( ( n .^ X ) .* ( T ` ( f ` n ) ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cI
    cn0
    wss
    #
    cI
    c0
    wne
    #
    wa
    #
    wa
    #
    cM
    cC
    vn
    cI
    vn
    cv
    #
    cX
    c.ex
    co
    #
    @8
    vf
    cv
    #
    cfv
    #
    cT
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    cM
    cC
    vn
    cI
    @9
    cM
    @8
    cdecpmat
    co
    #
    cT
    cfv
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wceq
    vf
    cM
    vx
    vk
    cB
    cI
    vi
    vj
    vx
    cv
    #
    cdm
    #
    cdm
    #
    @23
    vk
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    @21
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    cmpt2
    #
    ccur
    cfv
    #
    cD
    cI
    cmap
    co
    #
    @7
    @32
    vk
    cI
    vm
    cM
    vi
    vj
    cN
    cN
    @24
    @25
    @26
    vm
    cv
    #
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    csb
    #
    cmpt
    #
    @33
    @7
    @32
    vk
    cI
    vx
    cM
    @30
    csb
    #
    cmpt
    #
    @40
    @7
    @32
    vl
    cI
    vy
    cM
    vi
    vj
    vy
    cv
    #
    cdm
    #
    cdm
    #
    @45
    vl
    cv
    #
    @25
    @26
    @43
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    csb
    #
    cmpt
    @42
    @7
    vy
    vl
    cM
    @50
    @31
    cvv
    cvv
    cB
    cI
    vx
    vk
    vy
    vl
    cB
    cI
    @30
    @50
    vi
    vj
    @45
    @45
    @24
    @48
    cfv
    #
    cmpt2
    #
    vx
    vy
    weq
    #
    vi
    vj
    @23
    @23
    @29
    @45
    @45
    @52
    @54
    @22
    @44
    @21
    @43
    dmeq
    dmeqd
    #
    @55
    @54
    @24
    @28
    @48
    @54
    @27
    @47
    cco1
    @25
    @26
    @21
    @43
    oveq
    fveq2d
    fveq1d
    mpt2eq123dv
    #
    vk
    vl
    weq
    vi
    vj
    @45
    @45
    @52
    @49
    @24
    @46
    @48
    fveq2
    mpt2eq3dv
    cbvmpt2v
    @7
    @50
    cvv
    wcel
    #
    vy
    vl
    cB
    cI
    @7
    @43
    cB
    wcel
    #
    @46
    cI
    wcel
    #
    wa
    wa
    @45
    cvv
    wcel
    #
    @60
    wa
    #
    @57
    @58
    @61
    @7
    @59
    @58
    @60
    @60
    @58
    @44
    cvv
    wcel
    @60
    @43
    cB
    dmexg
    @44
    cvv
    dmexg
    syl
    #
    @62
    jca
    ad2antrl
    vi
    vj
    @45
    @45
    @49
    cvv
    cvv
    mpt2exga
    syl
    ralrimivva
    @3
    @4
    @5
    simprr
    @4
    cI
    cvv
    wcel
    #
    @3
    @5
    cI
    cn0
    nn0ex
    ssex
    #
    ad2antrl
    #
    @3
    @2
    @6
    @0
    @1
    @2
    simp3
    #
    adantr
    #
    mpt2curryvald
    vl
    vk
    cI
    @51
    @41
    vl
    vk
    weq
    #
    @51
    vy
    cM
    @53
    csb
    @41
    @68
    vy
    cM
    @50
    @53
    @68
    vi
    vj
    @45
    @45
    @49
    @52
    @46
    @24
    @48
    fveq2
    mpt2eq3dv
    csbeq2dv
    vy
    vx
    cM
    @53
    @30
    @54
    @30
    @53
    wceq
    vy
    vx
    weq
    @53
    @30
    wceq
    @56
    @21
    @43
    eqcom
    @30
    @53
    eqcom
    3imtr3i
    cbvcsbv
    syl6eq
    cbvmptv
    syl6eq
    @7
    vk
    cI
    @41
    @39
    @3
    @41
    @39
    wceq
    @6
    @3
    @41
    vi
    vj
    cM
    cdm
    #
    cdm
    #
    @70
    @24
    @25
    @26
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cmpt2
    #
    @39
    @3
    vx
    cM
    @30
    @74
    cB
    @66
    @21
    cM
    wceq
    #
    @30
    @74
    wceq
    @3
    @75
    vi
    vj
    @23
    @23
    @29
    @70
    @70
    @73
    @75
    @22
    @69
    @21
    cM
    dmeq
    dmeqd
    #
    @76
    @75
    @24
    @28
    @72
    @75
    @27
    @71
    cco1
    @25
    @26
    @21
    cM
    oveq
    fveq2d
    fveq1d
    mpt2eq123dv
    adantl
    csbied
    @3
    vm
    cM
    @38
    @74
    cB
    @66
    @3
    @34
    cM
    wceq
    #
    wa
    #
    vi
    vj
    cN
    cN
    @37
    @70
    @70
    @73
    @3
    cN
    @70
    wceq
    #
    @77
    @2
    @0
    @79
    @1
    @2
    cM
    cP
    cbs
    cfv
    #
    cN
    cN
    cxp
    #
    cmap
    co
    wcel
    @81
    @80
    cM
    wf
    #
    @79
    cC
    cB
    cP
    @80
    cM
    cN
    pmatcollpw.c
    @80
    eqid
    #
    pmatcollpw.b
    matbas2i
    cM
    @80
    @81
    elmapi
    @82
    @70
    @81
    cdm
    cN
    @82
    @69
    @81
    @81
    @80
    cM
    fdm
    dmeqd
    cN
    dmxpid
    syl6req
    3syl
    3ad2ant3
    adantr
    #
    @84
    @78
    @24
    @36
    @72
    @78
    @35
    @71
    cco1
    @78
    @34
    cM
    @25
    @26
    @3
    @77
    simpr
    oveqd
    fveq2d
    fveq1d
    mpt2eq123dv
    csbied
    eqtr4d
    adantr
    mpteq2dv
    eqtrd
    @7
    @40
    @33
    wcel
    #
    cI
    cD
    @40
    wf
    #
    @7
    vk
    cI
    @39
    cD
    @40
    @7
    @24
    cI
    wcel
    #
    wa
    #
    @39
    vi
    vj
    cN
    cN
    @73
    cmpt2
    #
    cD
    @3
    @39
    @89
    wceq
    @6
    @87
    @3
    vm
    cM
    @38
    @89
    cB
    @66
    @78
    vi
    vj
    cN
    cN
    @37
    @73
    @78
    @24
    @36
    @72
    @78
    @35
    @71
    cco1
    @77
    @35
    @71
    wceq
    @3
    @25
    @26
    @34
    cM
    oveq
    adantl
    fveq2d
    fveq1d
    mpt2eq3dv
    csbied
    ad2antrr
    @88
    vi
    vj
    cA
    cD
    @73
    cR
    cR
    cbs
    cfv
    #
    cN
    ccrg
    pmatcollpw3.a
    @90
    eqid
    #
    pmatcollpw3.d
    @0
    @1
    @2
    @6
    @87
    simpll1
    @0
    @1
    @2
    @6
    @87
    simpll2
    @88
    @25
    cN
    wcel
    #
    @26
    cN
    wcel
    #
    w3a
    #
    @71
    @80
    wcel
    @24
    cn0
    wcel
    #
    @73
    @90
    wcel
    @94
    cC
    cB
    cP
    @25
    @26
    @80
    cM
    cN
    pmatcollpw.c
    @83
    pmatcollpw.b
    @88
    @92
    @93
    simp2
    @88
    @92
    @93
    simp3
    @88
    @92
    @2
    @93
    @7
    @2
    @87
    @67
    adantr
    3ad2ant1
    matecld
    @88
    @92
    @95
    @93
    @7
    @87
    @95
    @4
    @87
    @95
    wi
    @3
    @5
    cI
    cn0
    @24
    ssel
    ad2antrl
    imp
    3ad2ant1
    @72
    @80
    cP
    cR
    @71
    @90
    @24
    @72
    eqid
    @83
    pmatcollpw.p
    @91
    coe1fvalcl
    syl2anc
    matbas2d
    eqeltrd
    @40
    eqid
    fmptd
    @3
    cD
    cvv
    wcel
    #
    @63
    @85
    @86
    wb
    @6
    @96
    @3
    cD
    cA
    cbs
    cfv
    cvv
    pmatcollpw3.d
    cA
    cbs
    fvex
    eqeltri
    a1i
    @4
    @63
    @5
    @64
    adantr
    cD
    cI
    @40
    cvv
    cvv
    elmapg
    syl2an
    mpbird
    eqeltrd
    @7
    @10
    @32
    wceq
    #
    wa
    #
    @15
    @20
    cM
    @98
    @14
    @19
    cC
    cgsu
    @98
    vn
    cI
    @13
    @18
    @98
    @8
    cI
    wcel
    #
    wa
    #
    @12
    @17
    @9
    c.as
    @100
    @12
    cM
    @8
    cdecpmat
    cB
    cI
    cxp
    #
    cres
    #
    co
    #
    cT
    cfv
    @17
    @100
    @11
    @103
    cT
    @100
    @11
    @8
    @32
    cfv
    #
    @103
    @98
    @11
    @104
    wceq
    #
    @99
    @97
    @105
    @7
    @8
    @10
    @32
    fveq1
    adantl
    adantr
    @7
    @99
    @104
    @103
    wceq
    @97
    @7
    @99
    wa
    #
    @104
    cM
    @8
    @31
    co
    @103
    @106
    vx
    vk
    cM
    @8
    @30
    @31
    cvv
    cvv
    cB
    cI
    @31
    eqid
    @106
    @30
    cvv
    wcel
    #
    vx
    vk
    cB
    cI
    @106
    @21
    cB
    wcel
    #
    @87
    wa
    wa
    @23
    cvv
    wcel
    #
    @109
    wa
    #
    @107
    @108
    @110
    @106
    @87
    @108
    @109
    @109
    @108
    @22
    cvv
    wcel
    @109
    @21
    cB
    dmexg
    @22
    cvv
    dmexg
    syl
    #
    @111
    jca
    ad2antrl
    vi
    vj
    @23
    @23
    @29
    cvv
    cvv
    mpt2exga
    syl
    ralrimivva
    @7
    @63
    @99
    @65
    adantr
    @7
    @2
    @99
    @67
    adantr
    @7
    @99
    simpr
    fvmpt2curryd
    @106
    @31
    @102
    cM
    @8
    @106
    @102
    vx
    vk
    cvv
    cn0
    @30
    cmpt2
    #
    @101
    cres
    #
    @31
    cdecpmat
    @112
    @101
    vi
    vj
    vk
    vx
    df-decpmat
    reseq1i
    @106
    cB
    cvv
    wss
    #
    @4
    wa
    #
    @113
    @31
    wceq
    @7
    @115
    @99
    @3
    @114
    @6
    @4
    @114
    @3
    cB
    ssv
    a1i
    @4
    @5
    simpl
    anim12i
    adantr
    vx
    vk
    cvv
    cn0
    cB
    cI
    @30
    resmpt2
    syl
    syl5req
    oveqd
    eqtrd
    adantlr
    eqtrd
    fveq2d
    @100
    @103
    @16
    cT
    @98
    @2
    @99
    @103
    @16
    wceq
    @3
    @2
    @6
    @97
    @66
    ad2antrr
    cM
    @8
    cB
    cI
    cdecpmat
    ovres
    sylan
    fveq2d
    eqtrd
    oveq2d
    mpteq2dva
    oveq2d
    eqeq2d
    rspcedv
end
