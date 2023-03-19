include "chil.mm"
include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "chfs.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cmpt.mm"
include "hfsmval.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem hfsval
  let cA: class A
  let cS: class S
  let cT: class T
  let vx: setvar x
  let cB: class B


  assert |- ( ( S : ~H --> CC /\ T : ~H --> CC /\ A e. ~H ) -> ( ( S +fn T ) ` A ) = ( ( S ` A ) + ( T ` A ) ) )

  proof
    chil
    cc
    cS
    wf
    #
    chil
    cc
    cT
    wf
    #
    cA
    chil
    wcel
    #
    cA
    cS
    cT
    chfs
    co
    #
    cfv
    #
    cA
    cS
    cfv
    #
    cA
    cT
    cfv
    #
    caddc
    co
    #
    wceq
    @0
    @1
    wa
    #
    @2
    @4
    cA
    vx
    chil
    vx
    cv
    #
    cS
    cfv
    #
    @9
    cT
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cfv
    @7
    @8
    cA
    @3
    @13
    vx
    cS
    cT
    hfsmval
    fveq1d
    vx
    cA
    @12
    @7
    chil
    @13
    @9
    cA
    wceq
    @10
    @5
    @11
    @6
    caddc
    @9
    cA
    cS
    fveq2
    @9
    cA
    cT
    fveq2
    oveq12d
    @13
    eqid
    @5
    @6
    caddc
    ovex
    fvmpt
    sylan9eq
    3impa
end
