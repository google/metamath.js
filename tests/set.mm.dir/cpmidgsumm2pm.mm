include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cpmidgsum.mm"
include "wa.mm"
include "cbs.mm"
include "wceq.mm"
include "3simpa.mm"
include "adantr.mm"
include "eqid.mm"
include "chpmatply1.mm"
include "syl5eqel.mm"
include "coe1fvalcl.mm"
include "sylan.mm"
include "crg.mm"
include "crngring.mm"
include "anim2i.mm"
include "matring.mm"
include "ringidcl.mm"
include "3syl.mm"
include "3adant3.mm"
include "mat2pmatlin.mm"
include "syl12anc.mm"
include "crh.mm"
include "mat2pmatrhm.mm"
include "rhm1.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem cpmidgsumm2pm
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let c.ex: class .^
  let cH: class H
  let c.as: class .*
  let cK: class K
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x
  assume cpmidgsum.a: |- A = ( N Mat R )
  assume cpmidgsum.b: |- B = ( Base ` A )
  assume cpmidgsum.p: |- P = ( Poly1 ` R )
  assume cpmidgsum.y: |- Y = ( N Mat P )
  assume cpmidgsum.x: |- X = ( var1 ` R )
  assume cpmidgsum.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume cpmidgsum.m: |- .x. = ( .s ` Y )
  assume cpmidgsum.1: |- .1. = ( 1r ` Y )
  assume cpmidgsum.u: |- U = ( algSc ` P )
  assume cpmidgsum.c: |- C = ( N CharPlyMat R )
  assume cpmidgsum.k: |- K = ( C ` M )
  assume cpmidgsum.h: |- H = ( K .x. .1. )
  assume cpmidgsumm2pm.o: |- O = ( 1r ` A )
  assume cpmidgsumm2pm.m: |- .* = ( .s ` A )
  assume cpmidgsumm2pm.t: |- T = ( N matToPolyMat R )

  disjoint A n
  disjoint B n
  disjoint H n
  disjoint K n
  disjoint X n
  disjoint N n
  disjoint P n
  disjoint R n
  disjoint Y n
  disjoint .^ n
  disjoint M n
  disjoint B k
  disjoint k n
  disjoint H k
  disjoint N k
  disjoint N l
  disjoint N x
  disjoint k l
  disjoint k x
  disjoint l n
  disjoint l x
  disjoint n x
  disjoint P k
  disjoint R k
  disjoint Y k
  disjoint Y l
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> H = ( Y gsum ( n e. NN0 |-> ( ( n .^ X ) .x. ( T ` ( ( ( coe1 ` K ) ` n ) .* O ) ) ) ) ) )

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
    cH
    cY
    vn
    cn0
    vn
    cv
    #
    cX
    c.ex
    co
    #
    @4
    cK
    cco1
    cfv
    #
    cfv
    #
    cU
    cfv
    #
    c.1
    c.x
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cY
    vn
    cn0
    @5
    @7
    cO
    c.as
    co
    cT
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cA
    cB
    cC
    cP
    cR
    c.x
    cU
    c.1
    vn
    c.ex
    cH
    cK
    cM
    cN
    cX
    cY
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    cpmidgsum.y
    cpmidgsum.x
    cpmidgsum.e
    cpmidgsum.m
    cpmidgsum.1
    cpmidgsum.u
    cpmidgsum.c
    cpmidgsum.k
    cpmidgsum.h
    cpmidgsum
    @3
    @11
    @14
    cY
    cgsu
    @3
    vn
    cn0
    @10
    @13
    @3
    @4
    cn0
    wcel
    #
    wa
    #
    @9
    @12
    @5
    c.x
    @16
    @12
    @8
    cO
    cT
    cfv
    #
    c.x
    co
    #
    @9
    @16
    @0
    @1
    wa
    #
    @7
    cR
    cbs
    cfv
    #
    wcel
    #
    cO
    cB
    wcel
    #
    @12
    @18
    wceq
    @3
    @19
    @15
    @0
    @1
    @2
    3simpa
    #
    adantr
    @3
    cK
    cP
    cbs
    cfv
    #
    wcel
    @15
    @21
    @3
    cK
    cM
    cC
    cfv
    @24
    cpmidgsum.k
    cA
    cB
    cC
    cP
    cR
    @24
    cM
    cN
    cpmidgsum.c
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    @24
    eqid
    #
    chpmatply1
    syl5eqel
    @6
    @24
    cP
    cR
    cK
    @20
    @4
    @6
    eqid
    @25
    cpmidgsum.p
    @20
    eqid
    #
    coe1fvalcl
    sylan
    @3
    @22
    @15
    @0
    @1
    @22
    @2
    @19
    @0
    cR
    crg
    wcel
    #
    wa
    cA
    crg
    wcel
    @22
    @1
    @27
    @0
    cR
    crngring
    anim2i
    cA
    cR
    cN
    cpmidgsum.a
    matring
    cB
    cA
    cO
    cpmidgsum.b
    cpmidgsumm2pm.o
    ringidcl
    3syl
    3adant3
    adantr
    cA
    cB
    cY
    cP
    cR
    cU
    cT
    c.as
    c.x
    cY
    cbs
    cfv
    #
    @20
    cN
    @7
    cO
    cpmidgsumm2pm.t
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    cpmidgsum.y
    @28
    eqid
    #
    @26
    cpmidgsum.u
    cpmidgsumm2pm.m
    cpmidgsum.m
    mat2pmatlin
    syl12anc
    @16
    @17
    c.1
    @8
    c.x
    @3
    @17
    c.1
    wceq
    #
    @15
    @3
    @19
    cT
    cA
    cY
    crh
    co
    wcel
    @30
    @23
    cA
    cB
    cY
    cP
    cR
    cT
    @28
    cN
    cpmidgsumm2pm.t
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    cpmidgsum.y
    @29
    mat2pmatrhm
    cA
    cY
    cO
    cT
    c.1
    cpmidgsumm2pm.o
    cpmidgsum.1
    rhm1
    3syl
    adantr
    oveq2d
    eqtr2d
    oveq2d
    mpteq2dva
    oveq2d
    eqtrd
end
