include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cabs.mm"
include "cjneg.mm"
include "oveq2d.mm"
include "wceq.mm"
include "cjcl.mm"
include "mul2neg.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "negcl.mm"
include "absval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem absneg
  let cA: class A


  assert |- ( A e. CC -> ( abs ` -u A ) = ( abs ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    #
    @1
    ccj
    cfv
    #
    cmul
    co
    #
    csqrt
    cfv
    #
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
    @1
    cabs
    cfv
    #
    cA
    cabs
    cfv
    @0
    @3
    @6
    csqrt
    @0
    @3
    @1
    @5
    cneg
    #
    cmul
    co
    #
    @6
    @0
    @2
    @8
    @1
    cmul
    cA
    cjneg
    oveq2d
    @0
    @5
    cc
    wcel
    @9
    @6
    wceq
    cA
    cjcl
    cA
    @5
    mul2neg
    mpdan
    eqtrd
    fveq2d
    @0
    @1
    cc
    wcel
    @7
    @4
    wceq
    cA
    negcl
    @1
    absval
    syl
    cA
    absval
    3eqtr4d
end
