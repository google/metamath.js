include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "oveq.mm"
include "mpteq2dv.mm"
include "oveq2d.mm"
include "mdetfval.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem mdetleib
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
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume mdetfval.d: |- D = ( N maDet R )
  assume mdetfval.a: |- A = ( N Mat R )
  assume mdetfval.b: |- B = ( Base ` A )
  assume mdetfval.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume mdetfval.y: |- Y = ( ZRHom ` R )
  assume mdetfval.s: |- S = ( pmSgn ` N )
  assume mdetfval.t: |- .x. = ( .r ` R )
  assume mdetfval.u: |- U = ( mulGrp ` R )

  disjoint p x
  disjoint M p
  disjoint M x
  disjoint N p
  disjoint N x
  disjoint R p
  disjoint R x
  disjoint y z
  disjoint m n
  disjoint m r
  disjoint B m
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint m p
  disjoint m x
  disjoint M m
  disjoint N m
  disjoint n p
  disjoint n x
  disjoint N n
  disjoint p r
  disjoint r x
  disjoint N r
  disjoint P m
  disjoint P n
  disjoint P r
  disjoint R m
  disjoint R n
  disjoint R r
  disjoint S m
  disjoint S n
  disjoint S r
  disjoint .x. m
  disjoint .x. n
  disjoint .x. r
  disjoint U m
  disjoint U n
  disjoint U r
  disjoint Y m
  disjoint Y n
  disjoint Y r
  assert |- ( M e. B -> ( D ` M ) = ( R gsum ( p e. P |-> ( ( ( Y o. S ) ` p ) .x. ( U gsum ( x e. N |-> ( ( p ` x ) M x ) ) ) ) ) ) )

  proof
    vm
    cM
    cR
    vp
    cP
    vp
    cv
    #
    cY
    cS
    ccom
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
    mdetfval.d
    mdetfval.a
    mdetfval.b
    mdetfval.p
    mdetfval.y
    mdetfval.s
    mdetfval.t
    mdetfval.u
    mdetfval
    cR
    @14
    cgsu
    ovex
    fvmpt
end
