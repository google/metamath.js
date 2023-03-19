include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cco1.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cpl1.mm"
include "cmat.mm"
include "cmat2pmat.mm"
include "cmgp.mm"
include "cmg.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "cmulr.mm"
include "csg.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "ccpmat.mm"
include "cmpt2.mm"
include "cfz.mm"
include "cmap.mm"
include "wrex.mm"
include "cn.mm"
include "ccpmat2mat.mm"
include "cur.mm"
include "cbs.mm"
include "eqid.mm"
include "eqeq1.mm"
include "breq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "cayhamlem4.mm"
include "wa.mm"
include "cpm2mfval.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "2rexbidv.mm"
include "mpbird.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "oveq2i.mm"
include "cayhamlem1.mm"
include "eqtrd.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "m2cpminv0.mm"
include "syl.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "sylan9eqr.mm"
include "mpdan.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem cayleyhamiltonALT
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vn: setvar n
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vj: setvar j
  let vb: setvar b
  let vl: setvar l
  let vs: setvar s
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume cayleyhamilton.a: |- A = ( N Mat R )
  assume cayleyhamilton.b: |- B = ( Base ` A )
  assume cayleyhamilton.0: |- .0. = ( 0g ` A )
  assume cayleyhamilton.c: |- C = ( N CharPlyMat R )
  assume cayleyhamilton.k: |- K = ( coe1 ` ( C ` M ) )
  assume cayleyhamilton.m: |- .* = ( .s ` A )
  assume cayleyhamilton.e: |- .^ = ( .g ` ( mulGrp ` A ) )

  disjoint A n
  disjoint B n
  disjoint C n
  disjoint M n
  disjoint N n
  disjoint R n
  disjoint .* n
  disjoint .^ n
  disjoint B j
  disjoint M j
  disjoint N j
  disjoint R j
  disjoint b j
  disjoint b l
  disjoint b n
  disjoint b s
  disjoint j l
  disjoint j n
  disjoint j s
  disjoint l n
  disjoint l s
  disjoint n s
  disjoint A b
  disjoint A m
  disjoint A s
  disjoint A x
  disjoint A y
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint B b
  disjoint B m
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint K b
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M m
  disjoint M s
  disjoint M x
  disjoint M y
  disjoint M l
  disjoint b l
  disjoint l n
  disjoint l s
  disjoint l x
  disjoint l y
  disjoint N b
  disjoint N m
  disjoint N s
  disjoint N x
  disjoint N y
  disjoint N l
  disjoint R b
  disjoint R m
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint R l
  disjoint .0. b
  disjoint .0. s
  disjoint .0. x
  disjoint .0. y
  disjoint .* m
  disjoint .* s
  disjoint .* x
  disjoint .* y
  disjoint .* b
  disjoint .^ b
  disjoint .^ m
  disjoint .^ s
  disjoint .^ x
  disjoint .^ y
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( A gsum ( n e. NN0 |-> ( ( K ` n ) .* ( n .^ M ) ) ) ) = .0. )

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
    cA
    vn
    cn0
    vn
    cv
    #
    cM
    cC
    cfv
    #
    cco1
    cfv
    #
    cfv
    #
    @4
    cM
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cN
    cR
    cpl1
    cfv
    #
    cmat
    co
    #
    vn
    cn0
    @4
    cM
    cN
    cR
    cmat2pmat
    co
    #
    cfv
    #
    @13
    cmgp
    cfv
    cmg
    cfv
    #
    co
    #
    @4
    vl
    cn0
    vl
    cv
    #
    cc0
    wceq
    #
    @13
    c0g
    cfv
    #
    @15
    cc0
    vb
    cv
    #
    cfv
    @14
    cfv
    @13
    cmulr
    cfv
    #
    co
    @13
    csg
    cfv
    #
    co
    #
    @18
    vs
    cv
    #
    c1
    caddc
    co
    #
    wceq
    #
    @25
    @21
    cfv
    @14
    cfv
    #
    @26
    @18
    clt
    wbr
    #
    @20
    @18
    c1
    cmin
    co
    #
    @21
    cfv
    #
    @14
    cfv
    #
    @15
    @18
    @21
    cfv
    #
    @14
    cfv
    #
    @22
    co
    #
    @23
    co
    #
    cif
    #
    cif
    #
    cif
    #
    cmpt
    #
    cfv
    #
    @22
    co
    #
    cmpt
    #
    cgsu
    co
    #
    vm
    cN
    cR
    ccpmat
    co
    #
    vx
    vy
    cN
    cN
    cc0
    vx
    cv
    vy
    cv
    vm
    cv
    co
    cco1
    cfv
    cfv
    cmpt2
    cmpt
    #
    cfv
    #
    wceq
    #
    vb
    cB
    cc0
    @25
    cfz
    co
    cmap
    co
    #
    wrex
    vs
    cn
    wrex
    #
    cA
    vn
    cn0
    @4
    cK
    cfv
    #
    @8
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.0
    wceq
    #
    @3
    @50
    @11
    @44
    cN
    cR
    ccpmat2mat
    co
    #
    cfv
    #
    wceq
    #
    vb
    @49
    wrex
    vs
    cn
    wrex
    cA
    cB
    cC
    @12
    cR
    @14
    @22
    @56
    cA
    cur
    cfv
    #
    vn
    @16
    c.ex
    @40
    c.as
    @5
    cM
    @23
    cN
    @13
    cbs
    cfv
    #
    @13
    @20
    vs
    vb
    cayleyhamilton.a
    cayleyhamilton.b
    @12
    eqid
    #
    @13
    eqid
    #
    @22
    eqid
    #
    @23
    eqid
    #
    @20
    eqid
    #
    @14
    eqid
    #
    cayleyhamilton.c
    @5
    eqid
    vl
    vn
    cn0
    @39
    @4
    cc0
    wceq
    #
    @24
    @4
    @26
    wceq
    #
    @28
    @26
    @4
    clt
    wbr
    #
    @20
    @4
    c1
    cmin
    co
    #
    @21
    cfv
    #
    @14
    cfv
    #
    @15
    @4
    @21
    cfv
    #
    @14
    cfv
    #
    @22
    co
    #
    @23
    co
    #
    cif
    #
    cif
    #
    cif
    @18
    @4
    wceq
    #
    @19
    @67
    @38
    @78
    @24
    @18
    @4
    cc0
    eqeq1
    @79
    @27
    @68
    @37
    @77
    @28
    @18
    @4
    @26
    eqeq1
    @79
    @29
    @69
    @36
    @76
    @20
    @18
    @4
    @26
    clt
    breq2
    @79
    @32
    @72
    @35
    @75
    @23
    @79
    @31
    @71
    @14
    @79
    @30
    @70
    @21
    @18
    @4
    c1
    cmin
    oveq1
    fveq2d
    fveq2d
    @79
    @34
    @74
    @15
    @22
    @79
    @33
    @73
    @14
    @18
    @4
    @21
    fveq2
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    ifbieq2d
    ifbieq2d
    cbvmptv
    #
    @60
    eqid
    @59
    eqid
    cayleyhamilton.m
    @56
    eqid
    #
    cayleyhamilton.e
    @16
    eqid
    #
    cayhamlem4
    @3
    @48
    @58
    vs
    vb
    cn
    @49
    @3
    @47
    @57
    @11
    @3
    @44
    @46
    @56
    @0
    @1
    @46
    @56
    wceq
    @2
    @0
    @1
    wa
    @56
    @46
    vx
    vy
    cR
    @45
    vm
    @56
    cN
    ccrg
    @81
    @45
    eqid
    #
    cpm2mfval
    eqcomd
    3adant3
    fveq1d
    eqeq2d
    2rexbidv
    mpbird
    @3
    @48
    @55
    vs
    vb
    cn
    @49
    @3
    @25
    cn
    wcel
    @21
    @49
    wcel
    wa
    #
    wa
    #
    @48
    @55
    @85
    @48
    wa
    @54
    @47
    c.0
    @85
    @48
    @54
    @47
    wceq
    @85
    @11
    @54
    @47
    @85
    @10
    @53
    cA
    cgsu
    @85
    vn
    cn0
    @9
    @52
    @85
    @4
    cn0
    wcel
    wa
    #
    @7
    @51
    @8
    c.as
    @86
    @4
    @6
    cK
    @6
    cK
    wceq
    @86
    cK
    @6
    cayleyhamilton.k
    eqcomi
    a1i
    fveq1d
    oveq1d
    mpteq2dva
    oveq2d
    eqeq1d
    biimpa
    @85
    @47
    c.0
    wceq
    #
    @48
    @85
    @44
    @20
    wceq
    #
    @87
    @85
    @44
    @13
    vj
    cn0
    vj
    cv
    #
    @15
    @16
    co
    #
    @89
    @40
    cfv
    #
    @22
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @20
    @44
    @94
    wceq
    @85
    @43
    @93
    @13
    cgsu
    vn
    vj
    cn0
    @42
    @92
    @4
    @89
    wceq
    @17
    @90
    @41
    @91
    @22
    @4
    @89
    @15
    @16
    oveq1
    @4
    @89
    @40
    fveq2
    oveq12d
    cbvmptv
    oveq2i
    a1i
    cA
    cB
    @12
    cR
    @14
    @22
    vj
    vn
    @16
    @40
    cM
    @23
    cN
    @13
    @20
    vs
    vb
    cayleyhamilton.a
    cayleyhamilton.b
    @61
    @62
    @63
    @64
    @65
    @66
    @80
    @82
    cayhamlem1
    eqtrd
    @88
    @85
    @47
    @20
    @46
    cfv
    #
    c.0
    @44
    @20
    @46
    fveq2
    @3
    @95
    c.0
    wceq
    @84
    @3
    @95
    cA
    c0g
    cfv
    #
    c.0
    @3
    @0
    cR
    crg
    wcel
    #
    wa
    #
    @95
    @96
    wceq
    @0
    @1
    @98
    @2
    @1
    @97
    @0
    cR
    crngring
    anim2i
    3adant3
    @98
    @95
    @20
    @56
    cfv
    @96
    @98
    @20
    @46
    @56
    @98
    @56
    @46
    vx
    vy
    cR
    @45
    vm
    @56
    cN
    crg
    @81
    @83
    cpm2mfval
    eqcomd
    fveq1d
    cA
    @13
    @12
    cR
    @56
    cN
    @96
    @20
    cayleyhamilton.a
    @81
    @61
    @62
    @96
    eqid
    @65
    m2cpminv0
    eqtrd
    syl
    cayleyhamilton.0
    syl6eqr
    adantr
    sylan9eqr
    mpdan
    adantr
    eqtrd
    ex
    rexlimdvva
    mpd
end
