include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "csp.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "hvmulcl.mm"
include "ax-his2.mm"
include "3expb.mm"
include "sylan.mm"
include "ax-his3.mm"
include "3expa.mm"
include "adantrl.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem hiassdi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. CC /\ B e. ~H ) /\ ( C e. ~H /\ D e. ~H ) ) -> ( ( ( A .h B ) +h C ) .ih D ) = ( ( A x. ( B .ih D ) ) + ( C .ih D ) ) )

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
    cC
    chil
    wcel
    #
    cD
    chil
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    csm
    co
    #
    cC
    cva
    co
    cD
    csp
    co
    #
    @7
    cD
    csp
    co
    #
    cC
    cD
    csp
    co
    #
    caddc
    co
    #
    cA
    cB
    cD
    csp
    co
    cmul
    co
    #
    @10
    caddc
    co
    @2
    @7
    chil
    wcel
    #
    @5
    @8
    @11
    wceq
    #
    cA
    cB
    hvmulcl
    @13
    @3
    @4
    @14
    @7
    cC
    cD
    ax-his2
    3expb
    sylan
    @6
    @9
    @12
    @10
    caddc
    @2
    @4
    @9
    @12
    wceq
    #
    @3
    @0
    @1
    @4
    @15
    cA
    cB
    cD
    ax-his3
    3expa
    adantrl
    oveq1d
    eqtrd
end
