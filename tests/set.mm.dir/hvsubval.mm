include "chil.mm"
include "cv.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cmv.mm"
include "oveq1.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "df-hvsub.mm"
include "ovex.mm"
include "ovmpt2.mm"

theorem hvsubval
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A -h B ) = ( A +h ( -u 1 .h B ) ) )

  proof
    vx
    vy
    cA
    cB
    chil
    chil
    vx
    cv
    #
    c1
    cneg
    #
    vy
    cv
    #
    csm
    co
    #
    cva
    co
    cA
    @1
    cB
    csm
    co
    #
    cva
    co
    cmv
    cA
    @3
    cva
    co
    @0
    cA
    @3
    cva
    oveq1
    @2
    cB
    wceq
    @3
    @4
    cA
    cva
    @2
    cB
    @1
    csm
    oveq2
    oveq2d
    vx
    vy
    df-hvsub
    cA
    @4
    cva
    ovex
    ovmpt2
end
