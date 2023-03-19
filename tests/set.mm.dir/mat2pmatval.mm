include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "mat2pmatfval.mm"
include "3adant3.mm"
include "oveq.mm"
include "fveq2d.mm"
include "mpt2eq3dv.mm"
include "adantl.mm"
include "simp3.mm"
include "simp1.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "fvmptd.mm"

theorem mat2pmatval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  assume mat2pmatfval.t: |- T = ( N matToPolyMat R )
  assume mat2pmatfval.a: |- A = ( N Mat R )
  assume mat2pmatfval.b: |- B = ( Base ` A )
  assume mat2pmatfval.p: |- P = ( Poly1 ` R )
  assume mat2pmatfval.s: |- S = ( algSc ` P )

  disjoint x y
  disjoint N x
  disjoint N y
  disjoint R x
  disjoint R y
  disjoint M x
  disjoint M y
  disjoint m n
  disjoint m r
  disjoint B m
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint n x
  disjoint n y
  disjoint N n
  disjoint m x
  disjoint m y
  disjoint N m
  disjoint r x
  disjoint r y
  disjoint N r
  disjoint R n
  disjoint R m
  disjoint R r
  disjoint S n
  disjoint S r
  disjoint V n
  disjoint V r
  disjoint M m
  disjoint S m
  disjoint V m
  assert |- ( ( N e. Fin /\ R e. V /\ M e. B ) -> ( T ` M ) = ( x e. N , y e. N |-> ( S ` ( x M y ) ) ) )

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
    vx
    vy
    cN
    cN
    vx
    cv
    #
    vy
    cv
    #
    vm
    cv
    #
    co
    #
    cS
    cfv
    #
    cmpt2
    #
    vx
    vy
    cN
    cN
    @4
    @5
    cM
    co
    #
    cS
    cfv
    #
    cmpt2
    #
    cB
    cT
    cvv
    @0
    @1
    cT
    vm
    cB
    @9
    cmpt
    wceq
    @2
    vx
    vy
    cA
    cB
    cP
    cR
    cS
    cT
    vm
    cN
    cV
    mat2pmatfval.t
    mat2pmatfval.a
    mat2pmatfval.b
    mat2pmatfval.p
    mat2pmatfval.s
    mat2pmatfval
    3adant3
    @6
    cM
    wceq
    #
    @9
    @12
    wceq
    @3
    @13
    vx
    vy
    cN
    cN
    @8
    @11
    @13
    @7
    @10
    cS
    @4
    @5
    @6
    cM
    oveq
    fveq2d
    mpt2eq3dv
    adantl
    @0
    @1
    @2
    simp3
    @3
    @0
    @0
    @12
    cvv
    wcel
    @0
    @1
    @2
    simp1
    #
    @14
    vx
    vy
    cN
    cN
    @11
    cfn
    cfn
    mpt2exga
    syl2anc
    fvmptd
end
