include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "w3a.mm"
include "csm.mm"
include "co.mm"
include "cmv.mm"
include "cfv.mm"
include "wceq.mm"
include "hvmulcl.mm"
include "lnopsubi.mm"
include "stoic3.mm"
include "lnopmuli.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem lnopmulsubi
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  assume lnopl.1: |- T e. LinOp


  assert |- ( ( A e. CC /\ B e. ~H /\ C e. ~H ) -> ( T ` ( ( A .h B ) -h C ) ) = ( ( A .h ( T ` B ) ) -h ( T ` C ) ) )

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
    cA
    cB
    csm
    co
    #
    cC
    cmv
    co
    cT
    cfv
    #
    @4
    cT
    cfv
    #
    cC
    cT
    cfv
    #
    cmv
    co
    #
    cA
    cB
    cT
    cfv
    csm
    co
    #
    @7
    cmv
    co
    @0
    @1
    @4
    chil
    wcel
    @2
    @5
    @8
    wceq
    cA
    cB
    hvmulcl
    @4
    cC
    cT
    lnopl.1
    lnopsubi
    stoic3
    @3
    @6
    @9
    @7
    cmv
    @0
    @1
    @6
    @9
    wceq
    @2
    cA
    cB
    cT
    lnopl.1
    lnopmuli
    3adant3
    oveq1d
    eqtrd
end
