include "cgr.mm"
include "wcel.mm"
include "cgs.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cvv.mm"
include "wceq.mm"
include "crn.mm"
include "rnexg.mm"
include "syl5eqel.mm"
include "mpt2exga.mm"
include "syl2anc.mm"
include "cgn.mm"
include "rneq.mm"
include "syl6eqr.mm"
include "id.mm"
include "eqidd.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "mpt2eq123dv.mm"
include "df-gdiv.mm"
include "fvmptg.mm"
include "mpdan.mm"
include "syl5eq.mm"

theorem grpodivfval
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cG: class G
  let cN: class N
  let cX: class X
  let cA: class A
  let cB: class B
  let vg: setvar g
  assume grpdiv.1: |- X = ran G
  assume grpdiv.2: |- N = ( inv ` G )
  assume grpdiv.3: |- D = ( /g ` G )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint N g
  disjoint X g
  assert |- ( G e. GrpOp -> D = ( x e. X , y e. X |-> ( x G ( N ` y ) ) ) )

  proof
    cG
    cgr
    wcel
    #
    cD
    cG
    cgs
    cfv
    #
    vx
    vy
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    cN
    cfv
    #
    cG
    co
    #
    cmpt2
    #
    grpdiv.3
    @0
    @6
    cvv
    wcel
    #
    @1
    @6
    wceq
    @0
    cX
    cvv
    wcel
    #
    @8
    @7
    @0
    cX
    cG
    crn
    #
    cvv
    grpdiv.1
    cG
    cgr
    rnexg
    syl5eqel
    #
    @10
    vx
    vy
    cX
    cX
    @5
    cvv
    cvv
    mpt2exga
    syl2anc
    vg
    cG
    vx
    vy
    vg
    cv
    #
    crn
    #
    @12
    @2
    @3
    @11
    cgn
    cfv
    #
    cfv
    #
    @11
    co
    #
    cmpt2
    @6
    cgr
    cvv
    cgs
    @11
    cG
    wceq
    #
    vx
    vy
    @12
    @12
    @15
    cX
    cX
    @5
    @16
    @12
    @9
    cX
    @11
    cG
    rneq
    grpdiv.1
    syl6eqr
    #
    @17
    @16
    @2
    @2
    @14
    @4
    @11
    cG
    @16
    id
    @16
    @2
    eqidd
    @16
    @3
    @13
    cN
    @16
    @13
    cG
    cgn
    cfv
    cN
    @11
    cG
    cgn
    fveq2
    grpdiv.2
    syl6eqr
    fveq1d
    oveq123d
    mpt2eq123dv
    vx
    vy
    vg
    df-gdiv
    fvmptg
    mpdan
    syl5eq
end
