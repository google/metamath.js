include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cshi.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cmin.mm"
include "simpr.mm"
include "addcl.mm"
include "shftval.mm"
include "syl2anc.mm"
include "pncan.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "ancoms.mm"

theorem shftval5
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( F shift A ) ` ( B + A ) ) = ( F ` B ) )

  proof
    cB
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cA
    caddc
    co
    #
    cF
    cA
    cshi
    co
    cfv
    #
    cB
    cF
    cfv
    #
    wceq
    @0
    @1
    wa
    #
    @3
    @2
    cA
    cmin
    co
    #
    cF
    cfv
    #
    @4
    @5
    @1
    @2
    cc
    wcel
    @3
    @7
    wceq
    @0
    @1
    simpr
    cB
    cA
    addcl
    cA
    @2
    cF
    shftfval.1
    shftval
    syl2anc
    @5
    @6
    cB
    cF
    cB
    cA
    pncan
    fveq2d
    eqtrd
    ancoms
end
