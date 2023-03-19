include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "cbs.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "w3a.mm"
include "eqid.mm"
include "chpmatply1.mm"
include "syl5eqel.mm"
include "cmat2pmat.mm"
include "pmatcollpwscmat.mm"
include "syld3an3.mm"

theorem cpmidgsum
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vn: setvar n
  let c.ex: class .^
  let cH: class H
  let cK: class K
  let cM: class M
  let cN: class N
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
  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> H = ( Y gsum ( n e. NN0 |-> ( ( n .^ X ) .x. ( ( U ` ( ( coe1 ` K ) ` n ) ) .x. .1. ) ) ) ) )

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
    cK
    cP
    cbs
    cfv
    #
    wcel
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
    @4
    cK
    cco1
    cfv
    cfv
    cU
    cfv
    c.1
    c.x
    co
    c.x
    co
    cmpt
    cgsu
    co
    wceq
    @0
    @1
    @2
    w3a
    cK
    cM
    cC
    cfv
    @3
    cpmidgsum.k
    cA
    cB
    cC
    cP
    cR
    @3
    cM
    cN
    cpmidgsum.c
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.p
    @3
    eqid
    #
    chpmatply1
    syl5eqel
    cA
    cY
    cbs
    cfv
    #
    cY
    cB
    cP
    cK
    cR
    cU
    cN
    cR
    cmat2pmat
    co
    #
    cU
    c.1
    vn
    @3
    c.ex
    c.x
    cR
    cbs
    cfv
    #
    cH
    cN
    cX
    cpmidgsum.p
    cpmidgsum.y
    @6
    eqid
    cpmidgsum.m
    cpmidgsum.e
    cpmidgsum.x
    @7
    eqid
    cpmidgsum.a
    cpmidgsum.b
    cpmidgsum.u
    @8
    eqid
    @5
    cpmidgsum.u
    cpmidgsum.1
    cpmidgsum.h
    pmatcollpwscmat
    syld3an3
end
