include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "chft.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "hfmmval.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem hfmval
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  let cS: class S


  assert |- ( ( A e. CC /\ T : ~H --> CC /\ B e. ~H ) -> ( ( A .fn T ) ` B ) = ( A x. ( T ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    chil
    cc
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
    chft
    co
    #
    cfv
    #
    cA
    cB
    cT
    cfv
    #
    cmul
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
    cmul
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
    hfmmval
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
    cmul
    @8
    cB
    cT
    fveq2
    oveq2d
    @11
    eqid
    cA
    @5
    cmul
    ovex
    fvmpt
    sylan9eq
    3impa
end
