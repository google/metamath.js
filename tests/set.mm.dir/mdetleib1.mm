include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "oveq.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "mdetfval1.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem mdetleib1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cM: class M
  let cN: class N
  let cY: class Y
  let vp: setvar p
  let vm: setvar m
  assume mdetfval1.d: |- D = ( N maDet R )
  assume mdetfval1.a: |- A = ( N Mat R )
  assume mdetfval1.b: |- B = ( Base ` A )
  assume mdetfval1.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume mdetfval1.y: |- Y = ( ZRHom ` R )
  assume mdetfval1.s: |- S = ( pmSgn ` N )
  assume mdetfval1.t: |- .x. = ( .r ` R )
  assume mdetfval1.u: |- U = ( mulGrp ` R )

  disjoint B p
  disjoint p x
  disjoint N p
  disjoint N x
  disjoint P p
  disjoint R p
  disjoint R x
  disjoint M p
  disjoint M x
  disjoint m p
  disjoint B m
  disjoint m x
  disjoint N m
  disjoint P m
  disjoint R m
  disjoint S m
  disjoint U m
  disjoint Y m
  disjoint .x. m
  disjoint M m
  assert |- ( M e. B -> ( D ` M ) = ( R gsum ( p e. P |-> ( ( Y ` ( S ` p ) ) .x. ( U gsum ( x e. N |-> ( ( p ` x ) M x ) ) ) ) ) ) )

  proof
    vm
    cM
    cR
    vp
    cP
    vp
    cv
    #
    cS
    cfv
    cY
    cfv
    #
    cU
    vx
    cN
    vx
    cv
    #
    @0
    cfv
    #
    @2
    vm
    cv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cR
    vp
    cP
    @1
    cU
    vx
    cN
    @3
    @2
    cM
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cB
    cD
    @4
    cM
    wceq
    #
    @9
    @14
    cR
    cgsu
    @15
    vp
    cP
    @8
    @13
    @15
    @7
    @12
    @1
    c.x
    @15
    @6
    @11
    cU
    cgsu
    @15
    vx
    cN
    @5
    @10
    @3
    @2
    @4
    cM
    oveq
    mpteq2dv
    oveq2d
    oveq2d
    mpteq2dv
    oveq2d
    vx
    cA
    cB
    cD
    cP
    cR
    cS
    c.x
    cU
    vm
    cN
    cY
    vp
    mdetfval1.d
    mdetfval1.a
    mdetfval1.b
    mdetfval1.p
    mdetfval1.y
    mdetfval1.s
    mdetfval1.t
    mdetfval1.u
    mdetfval1
    cR
    @14
    cgsu
    ovex
    fvmpt
end
