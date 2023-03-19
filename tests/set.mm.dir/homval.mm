include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "chot.mm"
include "co.mm"
include "cfv.mm"
include "csm.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "hommval.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem homval
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  let cS: class S


  assert |- ( ( A e. CC /\ T : ~H --> ~H /\ B e. ~H ) -> ( ( A .op T ) ` B ) = ( A .h ( T ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    cB
    chil
    wcel
    #
    cB
    cA
    cT
    chot
    co
    #
    cfv
    #
    cA
    cB
    cT
    cfv
    #
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
    cB
    vx
    chil
    cA
    vx
    cv
    #
    cT
    cfv
    #
    csm
    co
    #
    cmpt
    #
    cfv
    @6
    @7
    cB
    @3
    @11
    vx
    cA
    cT
    hommval
    fveq1d
    vx
    cB
    @10
    @6
    chil
    @11
    @8
    cB
    wceq
    @9
    @5
    cA
    csm
    @8
    cB
    cT
    fveq2
    oveq2d
    @11
    eqid
    cA
    @5
    csm
    ovex
    fvmpt
    sylan9eq
    3impa
end
