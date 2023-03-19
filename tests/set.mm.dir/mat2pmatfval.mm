include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cmat2pmat.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cvv.mm"
include "cmat.mm"
include "cbs.mm"
include "cpl1.mm"
include "cascl.mm"
include "wceq.mm"
include "df-mat2pmat.mm"
include "a1i.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "eqtr2i.mm"
include "syl6eq.mm"
include "simpl.mm"
include "fveq2.mm"
include "adantl.mm"
include "fveq1d.mm"
include "mpt2eq123dv.mm"
include "mpteq12dv.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptexg.mm"
include "mp1i.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem mat2pmatfval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vm: setvar m
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  assume mat2pmatfval.t: |- T = ( N matToPolyMat R )
  assume mat2pmatfval.a: |- A = ( N Mat R )
  assume mat2pmatfval.b: |- B = ( Base ` A )
  assume mat2pmatfval.p: |- P = ( Poly1 ` R )
  assume mat2pmatfval.s: |- S = ( algSc ` P )

  disjoint B m
  disjoint m x
  disjoint m y
  disjoint N m
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint R m
  disjoint R x
  disjoint R y
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint n x
  disjoint n y
  disjoint N n
  disjoint r x
  disjoint r y
  disjoint N r
  disjoint R n
  disjoint R r
  disjoint S n
  disjoint S r
  disjoint V n
  disjoint V r
  assert |- ( ( N e. Fin /\ R e. V ) -> T = ( m e. B |-> ( x e. N , y e. N |-> ( S ` ( x m y ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cT
    cN
    cR
    cmat2pmat
    co
    vm
    cB
    vx
    vy
    cN
    cN
    vx
    cv
    vy
    cv
    vm
    cv
    co
    #
    cS
    cfv
    #
    cmpt2
    #
    cmpt
    #
    mat2pmatfval.t
    @2
    vn
    vr
    cN
    cR
    cfn
    cvv
    vm
    vn
    cv
    #
    vr
    cv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    vx
    vy
    @7
    @7
    @3
    @8
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    cmpt2
    #
    cmpt
    #
    @6
    cmat2pmat
    cvv
    cmat2pmat
    vn
    vr
    cfn
    cvv
    @15
    cmpt2
    wceq
    @2
    vx
    vy
    vm
    vn
    vr
    df-mat2pmat
    a1i
    @7
    cN
    wceq
    #
    @8
    cR
    wceq
    #
    wa
    #
    @15
    @6
    wceq
    @2
    @18
    vm
    @10
    @14
    cB
    @5
    @18
    @10
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cB
    @18
    @9
    @19
    cbs
    @7
    cN
    @8
    cR
    cmat
    oveq12
    fveq2d
    cB
    cA
    cbs
    cfv
    #
    @20
    mat2pmatfval.b
    cA
    @19
    cbs
    mat2pmatfval.a
    fveq2i
    eqtr2i
    syl6eq
    @18
    vx
    vy
    @7
    @7
    @13
    cN
    cN
    @4
    @16
    @17
    simpl
    #
    @22
    @18
    @3
    @12
    cS
    @18
    @12
    cR
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cS
    @17
    @12
    @24
    wceq
    @16
    @17
    @11
    @23
    cascl
    @8
    cR
    cpl1
    fveq2
    fveq2d
    adantl
    cS
    cP
    cascl
    cfv
    @24
    mat2pmatfval.s
    cP
    @23
    cascl
    mat2pmatfval.p
    fveq2i
    eqtr2i
    syl6eq
    fveq1d
    mpt2eq123dv
    mpteq12dv
    adantl
    @0
    @1
    simpl
    @1
    cR
    cvv
    wcel
    @0
    cR
    cV
    elex
    adantl
    cB
    cvv
    wcel
    @6
    cvv
    wcel
    @2
    cB
    @21
    cvv
    mat2pmatfval.b
    cA
    cbs
    fvex
    eqeltri
    vm
    cB
    @5
    cvv
    mptexg
    mp1i
    ovmpt2d
    syl5eq
end
