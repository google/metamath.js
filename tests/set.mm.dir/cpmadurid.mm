include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cmdat.mm"
include "cbs.mm"
include "wceq.mm"
include "crg.mm"
include "crngring.mm"
include "chmatcl.mm"
include "syl3an2.mm"
include "ply1crng.mm"
include "3ad2ant2.mm"
include "eqid.mm"
include "madurid.mm"
include "syl2anc.mm"
include "chpmatval.mm"
include "a1i.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem cpmadurid
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume cpmadurid.a: |- A = ( N Mat R )
  assume cpmadurid.b: |- B = ( Base ` A )
  assume cpmadurid.c: |- C = ( N CharPlyMat R )
  assume cpmadurid.p: |- P = ( Poly1 ` R )
  assume cpmadurid.y: |- Y = ( N Mat P )
  assume cpmadurid.x: |- X = ( var1 ` R )
  assume cpmadurid.t: |- T = ( N matToPolyMat R )
  assume cpmadurid.s: |- .- = ( -g ` Y )
  assume cpmadurid.m1: |- .x. = ( .s ` Y )
  assume cpmadurid.1: |- .1. = ( 1r ` Y )
  assume cpmadurid.i: |- I = ( ( X .x. .1. ) .- ( T ` M ) )
  assume cpmadurid.j: |- J = ( N maAdju P )
  assume cpmadurid.m2: |- .X. = ( .r ` Y )


  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( I .X. ( J ` I ) ) = ( ( C ` M ) .x. .1. ) )

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
    cI
    cJ
    cfv
    c.xp
    co
    #
    cI
    cN
    cP
    cmdat
    co
    #
    cfv
    #
    c.1
    c.x
    co
    #
    cM
    cC
    cfv
    #
    c.1
    c.x
    co
    @3
    cI
    cY
    cbs
    cfv
    #
    wcel
    #
    cP
    ccrg
    wcel
    #
    @4
    @7
    wceq
    @1
    @0
    cR
    crg
    wcel
    @2
    @10
    cR
    crngring
    cA
    cB
    cP
    cR
    cT
    c.x
    c.1
    cI
    cM
    c.mi
    cN
    cX
    cY
    cpmadurid.a
    cpmadurid.b
    cpmadurid.p
    cpmadurid.y
    cpmadurid.x
    cpmadurid.t
    cpmadurid.s
    cpmadurid.m1
    cpmadurid.1
    cpmadurid.i
    chmatcl
    syl3an2
    @1
    @0
    @11
    @2
    cP
    cR
    cpmadurid.p
    ply1crng
    3ad2ant2
    cY
    @9
    @5
    cP
    c.x
    c.xp
    c.1
    cJ
    cI
    cN
    cpmadurid.y
    @9
    eqid
    cpmadurid.j
    @5
    eqid
    #
    cpmadurid.1
    cpmadurid.m2
    cpmadurid.m1
    madurid
    syl2anc
    @3
    @6
    @8
    c.1
    c.x
    @3
    @8
    cX
    c.1
    c.x
    co
    cM
    cT
    cfv
    c.mi
    co
    #
    @5
    cfv
    @6
    cA
    cB
    cC
    @5
    cP
    cR
    cT
    c.x
    c.1
    cM
    c.mi
    cN
    ccrg
    cX
    cY
    cpmadurid.c
    cpmadurid.a
    cpmadurid.b
    cpmadurid.p
    cpmadurid.y
    @12
    cpmadurid.s
    cpmadurid.x
    cpmadurid.m1
    cpmadurid.t
    cpmadurid.1
    chpmatval
    @3
    @13
    cI
    @5
    @3
    cI
    @13
    cI
    @13
    wceq
    @3
    cpmadurid.i
    a1i
    eqcomd
    fveq2d
    eqtr2d
    oveq1d
    eqtrd
end
