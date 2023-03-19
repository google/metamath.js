include "chil.mm"
include "wcel.mm"
include "ck.mm"
include "co.mm"
include "cfv.mm"
include "csp.mm"
include "csm.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "kbfval.mm"
include "fveq1d.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem kbval
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cT: class T


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( A ketbra B ) ` C ) = ( ( C .ih B ) .h A ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    cC
    cA
    cB
    ck
    co
    #
    cfv
    #
    cC
    cB
    csp
    co
    #
    cA
    csm
    co
    #
    wceq
    @0
    @1
    wa
    #
    @2
    @4
    cC
    vx
    chil
    vx
    cv
    #
    cB
    csp
    co
    #
    cA
    csm
    co
    #
    cmpt
    #
    cfv
    @6
    @7
    cC
    @3
    @11
    vx
    cA
    cB
    kbfval
    fveq1d
    vx
    cC
    @10
    @6
    chil
    @11
    @8
    cC
    wceq
    @9
    @5
    cA
    csm
    @8
    cC
    cB
    csp
    oveq1
    oveq1d
    @11
    eqid
    @5
    cA
    csm
    ovex
    fvmpt
    sylan9eq
    3impa
end
