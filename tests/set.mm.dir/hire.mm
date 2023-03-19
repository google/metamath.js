include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cr.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "hicl.mm"
include "cjreb.mm"
include "syl.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ax-his1.mm"
include "ancoms.mm"
include "eqeq2d.mm"
include "bitr4d.mm"

theorem hire
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A .ih B ) e. RR <-> ( A .ih B ) = ( B .ih A ) ) )

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
    cr
    wcel
    #
    @3
    @3
    ccj
    cfv
    #
    wceq
    #
    @3
    cB
    cA
    csp
    co
    #
    wceq
    @2
    @4
    @5
    @3
    wceq
    #
    @6
    @2
    @3
    cc
    wcel
    @4
    @8
    wb
    cA
    cB
    hicl
    @3
    cjreb
    syl
    @5
    @3
    eqcom
    syl6bb
    @2
    @7
    @5
    @3
    @1
    @0
    @7
    @5
    wceq
    cB
    cA
    ax-his1
    ancoms
    eqeq2d
    bitr4d
end
