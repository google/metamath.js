include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "ccj.mm"
include "cfv.mm"
include "fveq2.mm"
include "cj0.mm"
include "syl6eq.mm"
include "ax-his1.mm"
include "ancoms.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "impbid.mm"

theorem orthcom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A .ih B ) = 0 <-> ( B .ih A ) = 0 ) )

  proof
    cA
    chil
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
    csp
    co
    #
    cc0
    wceq
    #
    cB
    cA
    csp
    co
    #
    cc0
    wceq
    #
    @4
    @6
    @2
    @3
    ccj
    cfv
    #
    cc0
    wceq
    @4
    @7
    cc0
    ccj
    cfv
    #
    cc0
    @3
    cc0
    ccj
    fveq2
    cj0
    syl6eq
    @2
    @5
    @7
    cc0
    @1
    @0
    @5
    @7
    wceq
    cB
    cA
    ax-his1
    ancoms
    eqeq1d
    syl5ibr
    @6
    @4
    @2
    @5
    ccj
    cfv
    #
    cc0
    wceq
    @6
    @9
    @8
    cc0
    @5
    cc0
    ccj
    fveq2
    cj0
    syl6eq
    @2
    @3
    @9
    cc0
    cA
    cB
    ax-his1
    eqeq1d
    syl5ibr
    impbid
end
