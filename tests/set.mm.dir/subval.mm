include "cc.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "crio.mm"
include "cmin.mm"
include "eqeq2.mm"
include "riotabidv.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "df-sub.mm"
include "riotaex.mm"
include "ovmpt2.mm"

theorem subval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( A e. CC /\ B e. CC ) -> ( A - B ) = ( iota_ x e. CC ( B + x ) = A ) )

  proof
    vy
    vz
    cA
    cB
    cc
    cc
    vz
    cv
    #
    vx
    cv
    #
    caddc
    co
    #
    vy
    cv
    #
    wceq
    #
    vx
    cc
    crio
    cB
    @1
    caddc
    co
    #
    cA
    wceq
    #
    vx
    cc
    crio
    cmin
    @2
    cA
    wceq
    #
    vx
    cc
    crio
    @3
    cA
    wceq
    @4
    @7
    vx
    cc
    @3
    cA
    @2
    eqeq2
    riotabidv
    @0
    cB
    wceq
    #
    @7
    @6
    vx
    cc
    @8
    @2
    @5
    cA
    @0
    cB
    @1
    caddc
    oveq1
    eqeq1d
    riotabidv
    vy
    vz
    vx
    df-sub
    @6
    vx
    cc
    riotaex
    ovmpt2
end
