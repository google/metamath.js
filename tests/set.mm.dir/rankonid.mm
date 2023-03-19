include "cr1.mm"
include "cdm.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "wceq.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "rankonidlem.mm"
include "simprd.mm"
include "id.mm"
include "rankdmr1.mm"
include "syl6eqelr.mm"
include "impbii.mm"

theorem rankonid
  let cA: class A


  assert |- ( A e. dom R1 <-> ( rank ` A ) = A )

  proof
    cA
    cr1
    cdm
    #
    wcel
    #
    cA
    crnk
    cfv
    #
    cA
    wceq
    #
    @1
    cA
    cr1
    con0
    cima
    cuni
    wcel
    @3
    cA
    rankonidlem
    simprd
    @3
    cA
    @2
    @0
    @3
    id
    cA
    rankdmr1
    syl6eqelr
    impbii
end
