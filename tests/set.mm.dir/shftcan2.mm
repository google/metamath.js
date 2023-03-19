include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cshi.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "negneg.mm"
include "adantr.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "negcl.mm"
include "shftcan1.mm"
include "sylan.mm"
include "eqtr3d.mm"

theorem shftcan2
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( ( F shift -u A ) shift A ) ` B ) = ( F ` B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cB
    cF
    cA
    cneg
    #
    cshi
    co
    #
    @3
    cneg
    #
    cshi
    co
    #
    cfv
    #
    cB
    @4
    cA
    cshi
    co
    #
    cfv
    cB
    cF
    cfv
    #
    @2
    cB
    @6
    @8
    @2
    @5
    cA
    @4
    cshi
    @0
    @5
    cA
    wceq
    @1
    cA
    negneg
    adantr
    oveq2d
    fveq1d
    @0
    @3
    cc
    wcel
    @1
    @7
    @9
    wceq
    cA
    negcl
    @3
    cB
    cF
    shftfval.1
    shftcan1
    sylan
    eqtr3d
end
