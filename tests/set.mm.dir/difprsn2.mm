include "wne.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "prcom.mm"
include "difeq1i.mm"
include "wceq.mm"
include "necom.mm"
include "difprsn1.mm"
include "sylbi.mm"
include "syl5eq.mm"

theorem difprsn2
  let cA: class A
  let cB: class B


  assert |- ( A =/= B -> ( { A , B } \ { B } ) = { A } )

  proof
    cA
    cB
    wne
    #
    cA
    cB
    cpr
    #
    cB
    csn
    #
    cdif
    cB
    cA
    cpr
    #
    @2
    cdif
    #
    cA
    csn
    #
    @1
    @3
    @2
    cA
    cB
    prcom
    difeq1i
    @0
    cB
    cA
    wne
    @4
    @5
    wceq
    cA
    cB
    necom
    cB
    cA
    difprsn1
    sylbi
    syl5eq
end
