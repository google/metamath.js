include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "csh.mm"
include "wa.mm"
include "spansnsh.mm"
include "spansnid.mm"
include "jca.mm"
include "shmulcl.mm"
include "3com12.mm"
include "3expb.mm"
include "sylan2.mm"
include "ancoms.mm"

theorem spansnmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. CC ) -> ( B .h A ) e. ( span ` { A } ) )

  proof
    cB
    cc
    wcel
    #
    cA
    chil
    wcel
    #
    cB
    cA
    csm
    co
    cA
    csn
    cspn
    cfv
    #
    wcel
    #
    @1
    @0
    @2
    csh
    wcel
    #
    cA
    @2
    wcel
    #
    wa
    @3
    @1
    @4
    @5
    cA
    spansnsh
    cA
    spansnid
    jca
    @0
    @4
    @5
    @3
    @4
    @0
    @5
    @3
    cB
    cA
    @2
    shmulcl
    3com12
    3expb
    sylan2
    ancoms
end
