include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cn0.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "wceq.mm"
include "pm2mpval.mm"
include "3adant3.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "adantl.mm"
include "simp3.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem pm2mpfval
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  let vq: setvar q
  assume pm2mpval.p: |- P = ( Poly1 ` R )
  assume pm2mpval.c: |- C = ( N Mat P )
  assume pm2mpval.b: |- B = ( Base ` C )
  assume pm2mpval.m: |- .* = ( .s ` Q )
  assume pm2mpval.e: |- .^ = ( .g ` ( mulGrp ` Q ) )
  assume pm2mpval.x: |- X = ( var1 ` A )
  assume pm2mpval.a: |- A = ( N Mat R )
  assume pm2mpval.q: |- Q = ( Poly1 ` A )
  assume pm2mpval.t: |- T = ( N pMatToMatPoly R )

  disjoint N k
  disjoint R k
  disjoint M k
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint Q n
  disjoint Q r
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint V m
  disjoint V n
  disjoint V r
  disjoint X n
  disjoint X r
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a q
  disjoint a r
  disjoint k q
  disjoint m q
  disjoint n q
  disjoint q r
  disjoint .* n
  disjoint .* r
  disjoint .^ n
  disjoint .^ r
  disjoint M m
  disjoint Q m
  disjoint X m
  disjoint .* m
  disjoint .^ m
  assert |- ( ( N e. Fin /\ R e. V /\ M e. B ) -> ( T ` M ) = ( Q gsum ( k e. NN0 |-> ( ( M decompPMat k ) .* ( k .^ X ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vm
    cM
    cQ
    vk
    cn0
    vm
    cv
    #
    vk
    cv
    #
    cdecpmat
    co
    #
    @5
    cX
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
    cQ
    vk
    cn0
    cM
    @5
    cdecpmat
    co
    #
    @7
    c.as
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cB
    cT
    cvv
    @0
    @1
    cT
    vm
    cB
    @10
    cmpt
    wceq
    @2
    cA
    cB
    cC
    cP
    cQ
    cR
    cT
    vk
    vm
    c.ex
    c.as
    cN
    cV
    cX
    pm2mpval.p
    pm2mpval.c
    pm2mpval.b
    pm2mpval.m
    pm2mpval.e
    pm2mpval.x
    pm2mpval.a
    pm2mpval.q
    pm2mpval.t
    pm2mpval
    3adant3
    @4
    cM
    wceq
    #
    @10
    @14
    wceq
    @3
    @15
    @9
    @13
    cQ
    cgsu
    @15
    vk
    cn0
    @8
    @12
    @15
    @6
    @11
    @7
    c.as
    @4
    cM
    @5
    cdecpmat
    oveq1
    oveq1d
    mpteq2dv
    oveq2d
    adantl
    @0
    @1
    @2
    simp3
    @3
    cQ
    @13
    cgsu
    ovexd
    fvmptd
end
