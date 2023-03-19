include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "hvmulcl.mm"
include "lnopaddi.mm"
include "sylan2.mm"
include "3impb.mm"
include "3com12.mm"
include "lnopmuli.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem lnopaddmuli
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( T ` ( B +h ( A .h C ) ) ) = ( ( T ` B ) +h ( A .h ( T ` C ) ) ) )

  proof
    cA
    cc
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
    w3a
    #
    cB
    cA
    cC
    csm
    co
    #
    cva
    co
    cT
    cfv
    #
    cB
    cT
    cfv
    #
    @4
    cT
    cfv
    #
    cva
    co
    #
    @6
    cA
    cC
    cT
    cfv
    csm
    co
    #
    cva
    co
    @1
    @0
    @2
    @5
    @8
    wceq
    #
    @1
    @0
    @2
    @10
    @0
    @2
    wa
    @1
    @4
    chil
    wcel
    @10
    cA
    cC
    hvmulcl
    cB
    @4
    cT
    lnopl.1
    lnopaddi
    sylan2
    3impb
    3com12
    @3
    @7
    @9
    @6
    cva
    @0
    @2
    @7
    @9
    wceq
    @1
    cA
    cC
    cT
    lnopl.1
    lnopmuli
    3adant2
    oveq2d
    eqtrd
end
