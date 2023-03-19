include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cr.mm"
include "wceq.mm"
include "cjcj.mm"
include "oveq2d.mm"
include "cjcl.mm"
include "cjmul.mm"
include "mpdan.mm"
include "mulcom.mm"
include "3eqtr4d.mm"
include "wb.mm"
include "mulcl.mm"
include "cjreb.mm"
include "syl.mm"
include "mpbird.mm"

theorem cjmulrcl
  let cA: class A


  assert |- ( A e. CC -> ( A x. ( * ` A ) ) e. RR )

  proof
    cA
    cc
    wcel
    #
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    cr
    wcel
    #
    @2
    ccj
    cfv
    #
    @2
    wceq
    #
    @0
    @1
    @1
    ccj
    cfv
    #
    cmul
    co
    #
    @1
    cA
    cmul
    co
    #
    @4
    @2
    @0
    @6
    cA
    @1
    cmul
    cA
    cjcj
    oveq2d
    @0
    @1
    cc
    wcel
    #
    @4
    @7
    wceq
    cA
    cjcl
    #
    cA
    @1
    cjmul
    mpdan
    @0
    @9
    @2
    @8
    wceq
    @10
    cA
    @1
    mulcom
    mpdan
    3eqtr4d
    @0
    @2
    cc
    wcel
    #
    @3
    @5
    wb
    @0
    @9
    @11
    @10
    cA
    @1
    mulcl
    mpdan
    @2
    cjreb
    syl
    mpbird
end
