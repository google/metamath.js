include "cr.mm"
include "crp.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmo.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12.mm"
include "mpdan.mm"
include "oveq2.mm"
include "df-mod.mm"
include "ovex.mm"
include "ovmpt2.mm"

theorem modval
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( A mod B ) = ( A - ( B x. ( |_ ` ( A / B ) ) ) ) )

  proof
    vx
    vy
    cA
    cB
    cr
    crp
    vx
    cv
    #
    vy
    cv
    #
    @0
    @1
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cA
    cB
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    cmo
    cA
    @1
    cA
    @1
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @0
    cA
    wceq
    #
    @4
    @11
    wceq
    @5
    @12
    wceq
    @13
    @3
    @10
    @1
    cmul
    @13
    @2
    @9
    cfl
    @0
    cA
    @1
    cdiv
    oveq1
    fveq2d
    oveq2d
    @0
    cA
    @4
    @11
    cmin
    oveq12
    mpdan
    @1
    cB
    wceq
    #
    @11
    @8
    cA
    cmin
    @14
    @10
    @7
    wceq
    @11
    @8
    wceq
    @14
    @9
    @6
    cfl
    @1
    cB
    cA
    cdiv
    oveq2
    fveq2d
    @1
    cB
    @10
    @7
    cmul
    oveq12
    mpdan
    oveq2d
    vx
    vy
    df-mod
    cA
    @8
    cmin
    ovex
    ovmpt2
end
