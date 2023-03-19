include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "cmv.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "hvmulcl.mm"
include "lnopsubi.mm"
include "sylan2.mm"
include "3impb.mm"
include "3com12.mm"
include "lnopmuli.mm"
include "oveq2d.mm"
include "3adant2.mm"
include "eqtrd.mm"

theorem lnopsubmuli
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( T ` ( B -h ( A .h C ) ) ) = ( ( T ` B ) -h ( A .h ( T ` C ) ) ) )

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
    cB
    cA
    cC
    csm
    co
    #
    cmv
    co
    cT
    cfv
    #
    cB
    cT
    cfv
    #
    @3
    cT
    cfv
    #
    cmv
    co
    #
    @5
    cA
    cC
    cT
    cfv
    csm
    co
    #
    cmv
    co
    #
    @1
    @0
    @2
    @4
    @7
    wceq
    #
    @1
    @0
    @2
    @10
    @0
    @2
    wa
    #
    @1
    @3
    chil
    wcel
    @10
    cA
    cC
    hvmulcl
    cB
    @3
    cT
    lnopl.1
    lnopsubi
    sylan2
    3impb
    3com12
    @0
    @2
    @7
    @9
    wceq
    @1
    @11
    @6
    @8
    @5
    cmv
    cA
    cC
    cT
    lnopl.1
    lnopmuli
    oveq2d
    3adant2
    eqtrd
end
