include "cv.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cc.mm"
include "cabs.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12.mm"
include "mpdan.mm"
include "fveq2d.mm"
include "df-abs.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem absval
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( abs ` A ) = ( sqrt ` ( A x. ( * ` A ) ) ) )

  proof
    vx
    cA
    vx
    cv
    #
    @0
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    cc
    cabs
    @0
    cA
    wceq
    #
    @2
    @4
    csqrt
    @5
    @1
    @3
    wceq
    @2
    @4
    wceq
    @0
    cA
    ccj
    fveq2
    @0
    cA
    @1
    @3
    cmul
    oveq12
    mpdan
    fveq2d
    vx
    df-abs
    @4
    csqrt
    fvex
    fvmpt
end
