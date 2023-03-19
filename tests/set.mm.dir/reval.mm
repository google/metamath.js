include "cv.mm"
include "ccj.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cc.mm"
include "cre.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12.mm"
include "mpdan.mm"
include "oveq1d.mm"
include "df-re.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem reval
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( Re ` A ) = ( ( A + ( * ` A ) ) / 2 ) )

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
    caddc
    co
    #
    c2
    cdiv
    co
    cA
    cA
    ccj
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    cc
    cre
    @0
    cA
    wceq
    #
    @2
    @4
    c2
    cdiv
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
    caddc
    oveq12
    mpdan
    oveq1d
    vx
    df-re
    @4
    c2
    cdiv
    ovex
    fvmpt
end
