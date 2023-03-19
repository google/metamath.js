include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cmdat.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cgsu.mm"
include "eqid.mm"
include "chpmatval.mm"
include "cmat.mm"
include "cbs.mm"
include "wceq.mm"
include "csg.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "cvsca.mm"
include "cur.mm"
include "chmatcl.mm"
include "eqcomi.mm"
include "csymg.mm"
include "mdetleib.mm"
include "syl.mm"
include "eqtrd.mm"

theorem chpmatval2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let cG: class G
  let cH: class H
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  assume chpmatply1.c: |- C = ( N CharPlyMat R )
  assume chpmatply1.a: |- A = ( N Mat R )
  assume chpmatply1.b: |- B = ( Base ` A )
  assume chpmatply1.p: |- P = ( Poly1 ` R )
  assume chpmatval2.y: |- Y = ( N Mat P )
  assume chpmatval2.m1: |- .- = ( -g ` Y )
  assume chpmatval2.x: |- X = ( var1 ` R )
  assume chpmatval2.t1: |- .x. = ( .s ` Y )
  assume chpmatval2.t: |- T = ( N matToPolyMat R )
  assume chpmatval2.i: |- .1. = ( 1r ` Y )
  assume chpmatval2.g: |- G = ( SymGrp ` N )
  assume chpmatval2.h: |- H = ( Base ` G )
  assume chpmatval2.z: |- Z = ( ZRHom ` P )
  assume chpmatval2.s: |- S = ( pmSgn ` N )
  assume chpmatval2.u: |- U = ( mulGrp ` P )
  assume chpmatval2.rm: |- .X. = ( .r ` P )

  disjoint p x
  disjoint M p
  disjoint M x
  disjoint N p
  disjoint N x
  disjoint P p
  disjoint P x
  disjoint T p
  disjoint T x
  disjoint X p
  disjoint X x
  disjoint .x. p
  disjoint .x. x
  disjoint .1. p
  disjoint .1. x
  disjoint .- p
  disjoint .- x
  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( C ` M ) = ( P gsum ( p e. H |-> ( ( ( Z o. S ) ` p ) .X. ( U gsum ( x e. N |-> ( ( p ` x ) ( ( X .x. .1. ) .- ( T ` M ) ) x ) ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    cM
    cB
    wcel
    w3a
    #
    cM
    cC
    cfv
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
    cN
    cP
    cmdat
    co
    #
    cfv
    #
    cP
    vp
    cH
    vp
    cv
    #
    cZ
    cS
    ccom
    cfv
    cU
    vx
    cN
    vx
    cv
    #
    @4
    cfv
    @5
    @1
    co
    cmpt
    cgsu
    co
    c.xp
    co
    cmpt
    cgsu
    co
    #
    cA
    cB
    cC
    @2
    cP
    cR
    cT
    c.x
    c.1
    cM
    c.mi
    cN
    crg
    cX
    cY
    chpmatply1.c
    chpmatply1.a
    chpmatply1.b
    chpmatply1.p
    chpmatval2.y
    @2
    eqid
    #
    chpmatval2.m1
    chpmatval2.x
    chpmatval2.t1
    chpmatval2.t
    chpmatval2.i
    chpmatval
    @0
    @1
    cN
    cP
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @3
    @6
    wceq
    cA
    cB
    cP
    cR
    cT
    c.x
    c.1
    @1
    cM
    c.mi
    cN
    cX
    @8
    chpmatply1.a
    chpmatply1.b
    chpmatply1.p
    @8
    eqid
    chpmatval2.x
    chpmatval2.t
    c.mi
    cY
    csg
    cfv
    @8
    csg
    cfv
    chpmatval2.m1
    cY
    @8
    csg
    chpmatval2.y
    fveq2i
    eqtri
    c.x
    cY
    cvsca
    cfv
    @8
    cvsca
    cfv
    chpmatval2.t1
    cY
    @8
    cvsca
    chpmatval2.y
    fveq2i
    eqtri
    c.1
    cY
    cur
    cfv
    @8
    cur
    cfv
    chpmatval2.i
    cY
    @8
    cur
    chpmatval2.y
    fveq2i
    eqtri
    @1
    eqid
    chmatcl
    vx
    cY
    @9
    @2
    cH
    cP
    cS
    c.xp
    cU
    @1
    cN
    cZ
    vp
    @7
    chpmatval2.y
    @8
    cY
    cbs
    cY
    @8
    chpmatval2.y
    eqcomi
    fveq2i
    cH
    cG
    cbs
    cfv
    cN
    csymg
    cfv
    #
    cbs
    cfv
    chpmatval2.h
    cG
    @10
    cbs
    chpmatval2.g
    fveq2i
    eqtri
    chpmatval2.z
    chpmatval2.s
    chpmatval2.rm
    chpmatval2.u
    mdetleib
    syl
    eqtrd
end
