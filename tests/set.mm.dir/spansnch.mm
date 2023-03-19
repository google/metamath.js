include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cort.mm"
include "cch.mm"
include "spansn.mm"
include "wss.mm"
include "snssi.mm"
include "occl.mm"
include "choccl.mm"
include "3syl.mm"
include "eqeltrd.mm"

theorem spansnch
  let cA: class A


  assert |- ( A e. ~H -> ( span ` { A } ) e. CH )

  proof
    cA
    chil
    wcel
    #
    cA
    csn
    #
    cspn
    cfv
    @1
    cort
    cfv
    #
    cort
    cfv
    #
    cch
    cA
    spansn
    @0
    @1
    chil
    wss
    @2
    cch
    wcel
    @3
    cch
    wcel
    cA
    chil
    snssi
    @1
    occl
    @2
    choccl
    3syl
    eqeltrd
end
