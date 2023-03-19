include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cc0.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "cvsca.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "oveqi.mm"
include "w3a.mm"
include "ply1ring.mm"
include "anim2i.mm"
include "simpr.mm"
include "anim12i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "eqid.mm"
include "scmatscmide.mm"
include "sylan.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "fvif.mm"
include "fveq1i.mm"
include "iffv.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "ovif.mm"
include "csn.mm"
include "cxp.mm"
include "coe1z.mm"
include "ad2antlr.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpl.mm"
include "fvconst2g.mm"
include "syl.mm"
include "eqtrd.mm"
include "csca.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "0nn0.mm"
include "a1i.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "wb.mm"
include "ply1sca.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "adantr.mm"
include "mpbird.mm"
include "ifeq2d.mm"
include "cur.mm"
include "cbs.mm"
include "ancomd.mm"
include "coe1fvalcl.mm"
include "eqcomd.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "asclval.mm"
include "ply1idvr1.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "ifeq1d.mm"
include "3eqtrd.mm"

theorem pmatcollpwscmatlem1
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


  assert |- ( ( ( ( N e. Fin /\ R e. Ring ) /\ ( L e. NN0 /\ Q e. E ) ) /\ ( a e. N /\ b e. N ) ) -> ( ( ( coe1 ` ( a M b ) ) ` L ) ( .s ` P ) ( 0 ( .g ` ( mulGrp ` P ) ) ( var1 ` R ) ) ) = if ( a = b , ( U ` ( ( coe1 ` Q ) ` L ) ) , ( 0g ` P ) ) )

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
    va
    cv
    #
    cN
    wcel
    vb
    cv
    #
    cN
    wcel
    wa
    #
    wa
    #
    cL
    @7
    @8
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
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
    @7
    @8
    wceq
    #
    cL
    cQ
    cco1
    cfv
    #
    cfv
    #
    cL
    cP
    c0g
    cfv
    #
    cco1
    cfv
    #
    cfv
    #
    cif
    #
    @17
    @18
    co
    #
    @19
    @21
    @17
    @18
    co
    #
    @22
    cif
    #
    @19
    @21
    cU
    cfv
    #
    @22
    cif
    #
    @10
    @13
    @25
    @17
    @18
    @10
    @13
    cL
    @19
    cQ
    @22
    cif
    #
    cco1
    cfv
    #
    cfv
    #
    @25
    @10
    cL
    @12
    @32
    @10
    @11
    @31
    cco1
    @10
    @11
    @7
    @8
    cQ
    c.1
    c.as
    co
    #
    co
    #
    @31
    cM
    @34
    @7
    @8
    pmatcollpwscmat.m2
    oveqi
    @6
    @0
    cP
    crg
    wcel
    #
    @4
    w3a
    #
    @9
    @35
    @31
    wceq
    @6
    @0
    @36
    wa
    #
    @4
    wa
    @37
    @2
    @38
    @5
    @4
    @1
    @36
    @0
    cP
    cR
    pmatcollpwscmat.p
    ply1ring
    #
    anim2i
    @3
    @4
    simpr
    anim12i
    @0
    @36
    @4
    df-3an
    sylibr
    cC
    cE
    cQ
    cP
    c.1
    @7
    c.as
    @8
    cN
    @22
    pmatcollpwscmat.c
    pmatcollpwscmat.e2
    @22
    eqid
    #
    pmatcollpwscmat.1
    pmatcollpwscmat.m1
    scmatscmide
    sylan
    syl5eq
    fveq2d
    fveq1d
    @33
    cL
    @19
    @20
    @23
    cif
    #
    cfv
    @25
    cL
    @32
    @41
    @19
    cQ
    @22
    cco1
    fvif
    fveq1i
    @19
    cL
    @20
    @23
    iffv
    eqtri
    syl6eq
    oveq1d
    @10
    @26
    @19
    @27
    @24
    @17
    @18
    co
    #
    cif
    #
    @28
    @19
    @21
    @24
    @17
    @18
    ovif
    @6
    @43
    @28
    wceq
    @9
    @6
    @19
    @42
    @22
    @27
    @6
    @42
    cR
    c0g
    cfv
    #
    @17
    @18
    co
    #
    @22
    @6
    @24
    @44
    @17
    @18
    @6
    @24
    cL
    cn0
    @44
    csn
    cxp
    #
    cfv
    #
    @44
    @6
    cL
    @23
    @46
    @1
    @23
    @46
    wceq
    @0
    @5
    cP
    cR
    @44
    @22
    pmatcollpwscmat.p
    @40
    @44
    eqid
    coe1z
    ad2antlr
    fveq1d
    @6
    @44
    cvv
    wcel
    #
    @3
    wa
    @47
    @44
    wceq
    @2
    @48
    @5
    @3
    @2
    cR
    c0g
    fvexd
    @3
    @4
    simpl
    anim12i
    cn0
    @44
    cL
    cvv
    fvconst2g
    syl
    eqtrd
    oveq1d
    @6
    @45
    @22
    wceq
    #
    cP
    csca
    cfv
    #
    c0g
    cfv
    #
    @17
    @18
    co
    #
    @22
    wceq
    #
    @6
    cP
    clmod
    wcel
    #
    @17
    cE
    wcel
    #
    @53
    @1
    @54
    @0
    @5
    cP
    cR
    pmatcollpwscmat.p
    ply1lmod
    ad2antlr
    @1
    @55
    @0
    @5
    @1
    @15
    cmnd
    wcel
    #
    cc0
    cn0
    wcel
    #
    @14
    cE
    wcel
    @55
    @1
    @36
    @56
    @39
    cP
    @15
    @15
    eqid
    #
    ringmgp
    syl
    @57
    @1
    0nn0
    a1i
    cE
    cP
    cR
    @14
    @14
    eqid
    #
    pmatcollpwscmat.p
    pmatcollpwscmat.e2
    vr1cl
    cE
    @16
    @15
    cc0
    @14
    cE
    cP
    @15
    @58
    pmatcollpwscmat.e2
    mgpbas
    @16
    eqid
    #
    mulgnn0cl
    syl3anc
    ad2antlr
    @18
    @50
    @51
    cE
    cP
    @17
    @22
    pmatcollpwscmat.e2
    @50
    eqid
    #
    @18
    eqid
    #
    @51
    eqid
    @40
    lmod0vs
    syl2anc
    @2
    @49
    @53
    wb
    @5
    @2
    @45
    @52
    @22
    @2
    @44
    @51
    @17
    @18
    @2
    cR
    @50
    c0g
    @1
    cR
    @50
    wceq
    @0
    cP
    cR
    crg
    pmatcollpwscmat.p
    ply1sca
    #
    adantl
    fveq2d
    oveq1d
    eqeq1d
    adantr
    mpbird
    eqtrd
    ifeq2d
    adantr
    syl5eq
    @6
    @28
    @30
    wceq
    @9
    @6
    @19
    @27
    @29
    @22
    @6
    @29
    @21
    cP
    cur
    cfv
    #
    @18
    co
    #
    @27
    @6
    @21
    @50
    cbs
    cfv
    #
    wcel
    #
    @29
    @65
    wceq
    @6
    @67
    @21
    cK
    wcel
    #
    @6
    @4
    @3
    wa
    @68
    @6
    @3
    @4
    @2
    @5
    simpr
    ancomd
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
    @2
    @67
    @68
    wb
    @5
    @2
    @66
    cK
    @21
    @2
    @66
    cR
    cbs
    cfv
    cK
    @2
    @50
    cR
    cbs
    @1
    @50
    cR
    wceq
    @0
    @1
    cR
    @50
    @63
    eqcomd
    adantl
    fveq2d
    pmatcollpwscmat.k
    syl6eqr
    eleq2d
    adantr
    mpbird
    cU
    @18
    @64
    @50
    @66
    cP
    @21
    pmatcollpwscmat.u
    @61
    @66
    eqid
    @62
    @64
    eqid
    asclval
    syl
    @6
    @64
    @17
    @21
    @18
    @1
    @64
    @17
    wceq
    @0
    @5
    @1
    @17
    @64
    cP
    cR
    @16
    @15
    @14
    pmatcollpwscmat.p
    @59
    @58
    @60
    ply1idvr1
    eqcomd
    ad2antlr
    oveq2d
    eqtr2d
    ifeq1d
    adantr
    3eqtrd
end
