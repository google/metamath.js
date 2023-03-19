include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cort.mm"
include "cat.mm"
include "wceq.mm"
include "spansn.mm"
include "adantr.mm"
include "h1da.mm"
include "eqeltrd.mm"

theorem spansna
  let cA: class A


  assert |- ( ( A e. ~H /\ A =/= 0h ) -> ( span ` { A } ) e. HAtoms )

  proof
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    wa
    cA
    csn
    #
    cspn
    cfv
    #
    @2
    cort
    cfv
    cort
    cfv
    #
    cat
    @0
    @3
    @4
    wceq
    @1
    cA
    spansn
    adantr
    cA
    h1da
    eqeltrd
end
