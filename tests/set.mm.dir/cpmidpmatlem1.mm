include "cv.mm"
include "cco1.mm"
include "cfv.mm"
include "co.mm"
include "cn0.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem cpmidpmatlem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cH: class H
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let cY: class Y
  let vn: setvar n
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
  assume cpmidpmat.g: |- G = ( k e. NN0 |-> ( ( ( coe1 ` K ) ` k ) .* O ) )

  disjoint K k
  disjoint L k
  disjoint O k
  disjoint .* k
  disjoint B k
  disjoint H k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint Y k
  disjoint A n
  disjoint B n
  disjoint k n
  disjoint H n
  disjoint K n
  disjoint X n
  disjoint N l
  disjoint N n
  disjoint N x
  disjoint k l
  disjoint k x
  disjoint l n
  disjoint l x
  disjoint n x
  disjoint P n
  disjoint R n
  disjoint Y l
  disjoint Y n
  disjoint .^ n
  disjoint M n
  assert |- ( L e. NN0 -> ( G ` L ) = ( ( ( coe1 ` K ) ` L ) .* O ) )

  proof
    vk
    cL
    vk
    cv
    #
    cK
    cco1
    cfv
    #
    cfv
    #
    cO
    c.as
    co
    cL
    @1
    cfv
    #
    cO
    c.as
    co
    cn0
    cG
    @0
    cL
    wceq
    @2
    @3
    cO
    c.as
    @0
    cL
    @1
    fveq2
    oveq1d
    cpmidpmat.g
    @3
    cO
    c.as
    ovex
    fvmpt
end
