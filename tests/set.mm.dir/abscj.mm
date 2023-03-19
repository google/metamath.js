include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "wceq.mm"
include "cjcl.mm"
include "absval.mm"
include "syl.mm"
include "mulcom.mm"
include "mpdan.mm"
include "cjcj.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"

theorem abscj
  let cA: class A


  assert |- ( A e. CC -> ( abs ` ( * ` A ) ) = ( abs ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccj
    cfv
    #
    cabs
    cfv
    #
    cA
    @1
    cmul
    co
    #
    csqrt
    cfv
    #
    cA
    cabs
    cfv
    @0
    @2
    @1
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
    @4
    @0
    @1
    cc
    wcel
    #
    @2
    @7
    wceq
    cA
    cjcl
    #
    @1
    absval
    syl
    @0
    @3
    @6
    csqrt
    @0
    @3
    @1
    cA
    cmul
    co
    #
    @6
    @0
    @8
    @3
    @10
    wceq
    @9
    cA
    @1
    mulcom
    mpdan
    @0
    @5
    cA
    @1
    cmul
    cA
    cjcj
    oveq2d
    eqtr4d
    fveq2d
    eqtr4d
    cA
    absval
    eqtr4d
end
