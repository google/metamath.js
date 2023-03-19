include "cn0.mm"
include "cr.mm"
include "cv.mm"
include "cdp2.mm"
include "cdp.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "df-dp2.mm"
include "oveq1.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "syl6eqr.mm"
include "df-dp.mm"
include "ovexi.mm"
include "ovmpt2.mm"

theorem dpval
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN0 /\ B e. RR ) -> ( A . B ) = _ A B )

  proof
    vx
    vy
    cA
    cB
    cn0
    cr
    vx
    cv
    #
    vy
    cv
    #
    cdp2
    #
    cA
    cB
    cdp2
    #
    cdp
    cA
    @1
    c1
    cc0
    cdc
    #
    cdiv
    co
    #
    caddc
    co
    #
    @0
    cA
    wceq
    @2
    @0
    @5
    caddc
    co
    @6
    @0
    @1
    df-dp2
    @0
    cA
    @5
    caddc
    oveq1
    syl5eq
    @1
    cB
    wceq
    #
    @6
    cA
    cB
    @4
    cdiv
    co
    #
    caddc
    co
    @3
    @7
    @5
    @8
    cA
    caddc
    @1
    cB
    @4
    cdiv
    oveq1
    oveq2d
    cA
    cB
    df-dp2
    #
    syl6eqr
    vx
    vy
    df-dp
    @3
    cA
    @8
    caddc
    @9
    ovexi
    ovmpt2
end
