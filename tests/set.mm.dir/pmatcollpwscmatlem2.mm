include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cn0.mm"
include "cdecpmat.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cascl.mm"
include "cmpt2.mm"
include "cco1.mm"
include "w3a.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "adantr.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "1pmatscmul.mm"
include "syl5eqel.mm"
include "syl.mm"
include "simprl.mm"
include "decpmatcl.mm"
include "syl3anc.mm"
include "sylanbrc.mm"
include "eqid.mm"
include "mat2pmatval.mm"
include "3jca.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "decpmate.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "mpt2eq3dva.mm"
include "cc0.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "simp1lr.mm"
include "simp2.mm"
include "simp3.mm"
include "matecld.mm"
include "coe1fvalcl.mm"
include "ply1scltm.mm"
include "wral.mm"
include "c0g.mm"
include "cif.mm"
include "pmatcollpwscmatlem1.mm"
include "cvv.mm"
include "eqidd.mm"
include "oveq12.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "adantl.mm"
include "simprr.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "simpll.mm"
include "ply1ring.mm"
include "pm3.22.mm"
include "ply1sclcl.mm"
include "scmatscmide.mm"
include "sylan.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "wb.mm"
include "0nn0.mm"
include "a1i.mm"
include "ply1tmcl.mm"
include "matbas2d.mm"
include "eqmat.mm"
include "mpbird.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem pmatcollpwscmatlem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.1: class .1.
  let cE: class E
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  assume pmatcollpwscmat.p: |- P = ( Poly1 ` R )
  assume pmatcollpwscmat.c: |- C = ( N Mat P )
  assume pmatcollpwscmat.b: |- B = ( Base ` C )
  assume pmatcollpwscmat.m1: |- .* = ( .s ` C )
  assume pmatcollpwscmat.e1: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume pmatcollpwscmat.x: |- X = ( var1 ` R )
  assume pmatcollpwscmat.t: |- T = ( N matToPolyMat R )
  assume pmatcollpwscmat.a: |- A = ( N Mat R )
  assume pmatcollpwscmat.d: |- D = ( Base ` A )
  assume pmatcollpwscmat.u: |- U = ( algSc ` P )
  assume pmatcollpwscmat.k: |- K = ( Base ` R )
  assume pmatcollpwscmat.e2: |- E = ( Base ` P )
  assume pmatcollpwscmat.s: |- S = ( algSc ` P )
  assume pmatcollpwscmat.1: |- .1. = ( 1r ` C )
  assume pmatcollpwscmat.m2: |- M = ( Q .* .1. )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( L e. NN0 /\ Q e. E ) ) -> ( T ` ( M decompPMat L ) ) = ( ( U ` ( ( coe1 ` Q ) ` L ) ) .* .1. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cL
    cn0
    wcel
    #
    cQ
    cE
    wcel
    #
    wa
    #
    wa
    #
    cM
    cL
    cdecpmat
    co
    #
    cT
    cfv
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    vj
    cv
    #
    @7
    co
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    vi
    vj
    cN
    cN
    cL
    @9
    @10
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @12
    cfv
    #
    cmpt2
    #
    cL
    cQ
    cco1
    cfv
    #
    cfv
    #
    cU
    cfv
    #
    c.1
    c.as
    co
    #
    @6
    @0
    @1
    @7
    cD
    wcel
    #
    w3a
    #
    @8
    @14
    wceq
    @6
    @2
    @24
    @25
    @2
    @5
    simpl
    @6
    @1
    cM
    cB
    wcel
    #
    @3
    @24
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    #
    @6
    @0
    @1
    @4
    w3a
    #
    @26
    @6
    @2
    @4
    wa
    @28
    @5
    @4
    @2
    @3
    @4
    simpr
    anim2i
    @0
    @1
    @4
    df-3an
    sylibr
    @28
    cM
    cQ
    c.1
    c.as
    co
    cB
    pmatcollpwscmat.m2
    cB
    cC
    cP
    cQ
    cR
    c.1
    cE
    c.as
    cN
    pmatcollpwscmat.p
    pmatcollpwscmat.c
    pmatcollpwscmat.b
    pmatcollpwscmat.e2
    pmatcollpwscmat.m1
    pmatcollpwscmat.1
    1pmatscmul
    syl5eqel
    syl
    #
    @2
    @3
    @4
    simprl
    #
    cA
    cB
    cC
    cD
    cP
    cR
    cL
    cM
    cN
    crg
    pmatcollpwscmat.p
    pmatcollpwscmat.c
    pmatcollpwscmat.b
    pmatcollpwscmat.a
    pmatcollpwscmat.d
    decpmatcl
    syl3anc
    @0
    @1
    @24
    df-3an
    sylanbrc
    vi
    vj
    cA
    cD
    cP
    cR
    @12
    cT
    @7
    cN
    crg
    pmatcollpwscmat.t
    pmatcollpwscmat.a
    pmatcollpwscmat.d
    pmatcollpwscmat.p
    @12
    eqid
    #
    mat2pmatval
    syl
    @6
    vi
    vj
    cN
    cN
    @13
    @18
    @6
    @9
    cN
    wcel
    #
    @10
    cN
    wcel
    #
    w3a
    #
    @11
    @17
    @12
    @34
    @1
    @26
    @3
    w3a
    #
    @32
    @33
    wa
    @11
    @17
    wceq
    @6
    @32
    @35
    @33
    @6
    @1
    @26
    @3
    @27
    @29
    @30
    3jca
    3ad2ant1
    @6
    @32
    @33
    3simpc
    cB
    cC
    cP
    cR
    @9
    @10
    cL
    cM
    cN
    crg
    pmatcollpwscmat.p
    pmatcollpwscmat.c
    pmatcollpwscmat.b
    decpmate
    syl2anc
    fveq2d
    mpt2eq3dva
    @6
    @19
    vi
    vj
    cN
    cN
    @17
    cc0
    cR
    cv1
    cfv
    #
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cmpt2
    #
    @23
    @6
    vi
    vj
    cN
    cN
    @18
    @41
    @34
    @1
    @17
    cK
    wcel
    #
    @18
    @41
    wceq
    @0
    @1
    @5
    @32
    @33
    simp1lr
    #
    @34
    @15
    cE
    wcel
    @3
    @43
    @34
    cC
    cB
    cP
    @9
    @10
    cE
    cM
    cN
    pmatcollpwscmat.c
    pmatcollpwscmat.e2
    pmatcollpwscmat.b
    @6
    @32
    @33
    simp2
    @6
    @32
    @33
    simp3
    @6
    @32
    @26
    @33
    @29
    3ad2ant1
    matecld
    @6
    @32
    @3
    @33
    @30
    3ad2ant1
    @16
    cE
    cP
    cR
    @15
    cK
    cL
    @16
    eqid
    pmatcollpwscmat.e2
    pmatcollpwscmat.p
    pmatcollpwscmat.k
    coe1fvalcl
    syl2anc
    #
    @12
    cP
    cR
    @40
    @38
    @17
    cK
    @37
    @36
    pmatcollpwscmat.k
    pmatcollpwscmat.p
    @36
    eqid
    #
    @40
    eqid
    #
    @37
    eqid
    #
    @38
    eqid
    #
    @31
    ply1scltm
    syl2anc
    mpt2eq3dva
    @6
    @42
    @23
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    @42
    co
    #
    @51
    @52
    @23
    co
    #
    wceq
    #
    vb
    cN
    wral
    va
    cN
    wral
    #
    @6
    @55
    va
    vb
    cN
    cN
    @6
    @51
    cN
    wcel
    #
    @52
    cN
    wcel
    #
    wa
    #
    wa
    #
    cL
    @51
    @52
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    @39
    @40
    co
    #
    @51
    @52
    wceq
    @22
    cP
    c0g
    cfv
    #
    cif
    #
    @53
    @54
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    c.1
    cE
    c.ex
    c.as
    cK
    cL
    cM
    cN
    cX
    va
    vb
    pmatcollpwscmat.p
    pmatcollpwscmat.c
    pmatcollpwscmat.b
    pmatcollpwscmat.m1
    pmatcollpwscmat.e1
    pmatcollpwscmat.x
    pmatcollpwscmat.t
    pmatcollpwscmat.a
    pmatcollpwscmat.d
    pmatcollpwscmat.u
    pmatcollpwscmat.k
    pmatcollpwscmat.e2
    pmatcollpwscmat.s
    pmatcollpwscmat.1
    pmatcollpwscmat.m2
    pmatcollpwscmatlem1
    @60
    vi
    vj
    @51
    @52
    cN
    cN
    @41
    @64
    @42
    cvv
    @60
    @42
    eqidd
    @9
    @51
    wceq
    @10
    @52
    wceq
    wa
    #
    @41
    @64
    wceq
    @60
    @67
    @17
    @63
    @39
    @40
    @67
    cL
    @16
    @62
    @67
    @15
    @61
    cco1
    @9
    @51
    @10
    @52
    cM
    oveq12
    fveq2d
    fveq1d
    oveq1d
    adantl
    @6
    @57
    @58
    simprl
    @6
    @57
    @58
    simprr
    @60
    @63
    @39
    @40
    ovexd
    ovmpt2d
    @6
    @0
    cP
    crg
    wcel
    #
    @22
    cE
    wcel
    #
    w3a
    @59
    @54
    @66
    wceq
    @6
    @0
    @68
    @69
    @0
    @1
    @5
    simpll
    #
    @2
    @68
    @5
    @1
    @68
    @0
    cP
    cR
    pmatcollpwscmat.p
    ply1ring
    adantl
    adantr
    #
    @6
    @1
    @21
    cK
    wcel
    #
    @69
    @27
    @6
    @4
    @3
    wa
    #
    @72
    @5
    @73
    @2
    @3
    @4
    pm3.22
    adantl
    @20
    cE
    cP
    cR
    cQ
    cK
    cL
    @20
    eqid
    pmatcollpwscmat.e2
    pmatcollpwscmat.p
    pmatcollpwscmat.k
    coe1fvalcl
    syl
    cU
    cE
    cP
    cR
    @21
    cK
    pmatcollpwscmat.p
    pmatcollpwscmat.u
    pmatcollpwscmat.k
    pmatcollpwscmat.e2
    ply1sclcl
    syl2anc
    #
    3jca
    cC
    cE
    @22
    cP
    c.1
    @51
    c.as
    @52
    cN
    @65
    pmatcollpwscmat.c
    pmatcollpwscmat.e2
    @65
    eqid
    pmatcollpwscmat.1
    pmatcollpwscmat.m1
    scmatscmide
    sylan
    3eqtr4d
    ralrimivva
    @6
    @42
    cB
    wcel
    @23
    cB
    wcel
    #
    @50
    @56
    wb
    @6
    vi
    vj
    cC
    cB
    @41
    cP
    cE
    cN
    crg
    pmatcollpwscmat.c
    pmatcollpwscmat.e2
    pmatcollpwscmat.b
    @70
    @71
    @34
    @1
    @43
    cc0
    cn0
    wcel
    #
    @41
    cE
    wcel
    @44
    @45
    @76
    @34
    0nn0
    a1i
    cE
    @17
    cc0
    cP
    cR
    @40
    @38
    cK
    @37
    @36
    pmatcollpwscmat.k
    pmatcollpwscmat.p
    @46
    @47
    @48
    @49
    pmatcollpwscmat.e2
    ply1tmcl
    syl3anc
    matbas2d
    @6
    @0
    @1
    @69
    @75
    @70
    @27
    @74
    cB
    cC
    cP
    @22
    cR
    c.1
    cE
    c.as
    cN
    pmatcollpwscmat.p
    pmatcollpwscmat.c
    pmatcollpwscmat.b
    pmatcollpwscmat.e2
    pmatcollpwscmat.m1
    pmatcollpwscmat.1
    1pmatscmul
    syl3anc
    cC
    cB
    cP
    va
    vb
    cN
    @42
    @23
    pmatcollpwscmat.c
    pmatcollpwscmat.b
    eqmat
    syl2anc
    mpbird
    eqtrd
    3eqtrd
end
