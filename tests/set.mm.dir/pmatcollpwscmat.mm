include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cdecpmat.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cco1.mm"
include "wceq.mm"
include "crg.mm"
include "crngring.mm"
include "1pmatscmul.mm"
include "syl5eqel.mm"
include "syl3an2.mm"
include "pmatcollpw.mm"
include "syld3an3.mm"
include "wa.mm"
include "anim2i.mm"
include "3adant3.mm"
include "adantr.mm"
include "simp3.mm"
include "anim1i.mm"
include "ancomd.mm"
include "pmatcollpwscmatlem2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem pmatcollpwscmat
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
  let vn: setvar n
  let cE: class E
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  let cL: class L
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

  disjoint B n
  disjoint E n
  disjoint M n
  disjoint N n
  disjoint P n
  disjoint Q n
  disjoint R n
  disjoint X n
  disjoint .^ n
  disjoint E a
  disjoint E b
  disjoint E i
  disjoint E j
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i j
  disjoint L a
  disjoint L b
  disjoint L i
  disjoint L j
  disjoint M a
  disjoint M b
  disjoint M i
  disjoint M j
  disjoint N a
  disjoint N b
  disjoint N i
  disjoint N j
  disjoint P a
  disjoint P b
  disjoint P i
  disjoint P j
  disjoint Q a
  disjoint Q b
  disjoint Q i
  disjoint Q j
  disjoint R a
  disjoint R b
  disjoint R i
  disjoint R j
  disjoint U a
  disjoint U b
  disjoint .* a
  disjoint .* b
  disjoint .1. a
  disjoint .1. b
  assert |- ( ( N e. Fin /\ R e. CRing /\ Q e. E ) -> M = ( C gsum ( n e. NN0 |-> ( ( n .^ X ) .* ( ( U ` ( ( coe1 ` Q ) ` n ) ) .* .1. ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cQ
    cE
    wcel
    #
    w3a
    #
    cM
    cC
    vn
    cn0
    vn
    cv
    #
    cX
    c.ex
    co
    #
    cM
    @4
    cdecpmat
    co
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
    cC
    vn
    cn0
    @5
    @4
    cQ
    cco1
    cfv
    cfv
    cU
    cfv
    c.1
    c.as
    co
    #
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    @0
    @1
    @2
    cM
    cB
    wcel
    #
    cM
    @9
    wceq
    @1
    @0
    cR
    crg
    wcel
    #
    @2
    @13
    cR
    crngring
    #
    @0
    @14
    @2
    w3a
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
    syl3an2
    cB
    cC
    cP
    cR
    cT
    vn
    c.ex
    c.as
    cM
    cN
    cX
    pmatcollpwscmat.p
    pmatcollpwscmat.c
    pmatcollpwscmat.b
    pmatcollpwscmat.m1
    pmatcollpwscmat.e1
    pmatcollpwscmat.x
    pmatcollpwscmat.t
    pmatcollpw
    syld3an3
    @3
    @8
    @12
    cC
    cgsu
    @3
    vn
    cn0
    @7
    @11
    @3
    @4
    cn0
    wcel
    #
    wa
    #
    @6
    @10
    @5
    c.as
    @17
    @0
    @14
    wa
    #
    @16
    @2
    wa
    @6
    @10
    wceq
    @3
    @18
    @16
    @0
    @1
    @18
    @2
    @1
    @14
    @0
    @15
    anim2i
    3adant3
    adantr
    @17
    @2
    @16
    @3
    @2
    @16
    @0
    @1
    @2
    simp3
    anim1i
    ancomd
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
    @4
    cM
    cN
    cX
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
    pmatcollpwscmatlem2
    syl2anc
    oveq2d
    mpteq2dva
    oveq2d
    eqtrd
end
