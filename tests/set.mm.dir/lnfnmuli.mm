include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csm.mm"
include "co.mm"
include "c0v.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "ax-hv0cl.mm"
include "lnfnli.mm"
include "mp3an3.mm"
include "hvmulcl.mm"
include "ax-hvaddid.mm"
include "syl.mm"
include "fveq2d.mm"
include "cc0.mm"
include "lnfn0i.mm"
include "oveq2i.mm"
include "lnfnfi.mm"
include "ffvelrni.mm"
include "mulcl.mm"
include "sylan2.mm"
include "addid1d.mm"
include "syl5eq.mm"
include "3eqtr3d.mm"

theorem lnfnmuli
  let cA: class A
  let cB: class B
  let cT: class T
  assume lnfnl.1: |- T e. LinFn


  assert |- ( ( A e. CC /\ B e. ~H ) -> ( T ` ( A .h B ) ) = ( A x. ( T ` B ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cB
    csm
    co
    #
    c0v
    cva
    co
    #
    cT
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
    c0v
    cT
    cfv
    #
    caddc
    co
    #
    @3
    cT
    cfv
    @7
    @0
    @1
    c0v
    chil
    wcel
    @5
    @9
    wceq
    ax-hv0cl
    cA
    cB
    c0v
    cT
    lnfnl.1
    lnfnli
    mp3an3
    @2
    @4
    @3
    cT
    @2
    @3
    chil
    wcel
    @4
    @3
    wceq
    cA
    cB
    hvmulcl
    @3
    ax-hvaddid
    syl
    fveq2d
    @2
    @9
    @7
    cc0
    caddc
    co
    @7
    @8
    cc0
    @7
    caddc
    cT
    lnfnl.1
    lnfn0i
    oveq2i
    @2
    @7
    @1
    @0
    @6
    cc
    wcel
    @7
    cc
    wcel
    chil
    cc
    cB
    cT
    cT
    lnfnl.1
    lnfnfi
    ffvelrni
    cA
    @6
    mulcl
    sylan2
    addid1d
    syl5eq
    3eqtr3d
end
