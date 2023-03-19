include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wceq.mm"
include "spansnid.mm"
include "eleq2.mm"
include "syl5ibcom.mm"

theorem spansneleqi
  let cA: class A
  let cB: class B


  assert |- ( A e. ~H -> ( ( span ` { A } ) = ( span ` { B } ) -> A e. ( span ` { B } ) ) )

  proof
    cA
    chil
    wcel
    cA
    cA
    csn
    cspn
    cfv
    #
    wcel
    @0
    cB
    csn
    cspn
    cfv
    #
    wceq
    cA
    @1
    wcel
    cA
    spansnid
    @0
    @1
    cA
    eleq2
    syl5ibcom
end
