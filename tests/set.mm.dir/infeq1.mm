include "wceq.mm"
include "ccnv.mm"
include "csup.mm"
include "cinf.mm"
include "supeq1.mm"
include "df-inf.mm"
include "3eqtr4g.mm"

theorem infeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( B = C -> inf ( B , A , R ) = inf ( C , A , R ) )

  proof
    cB
    cC
    wceq
    cB
    cA
    cR
    ccnv
    #
    csup
    cC
    cA
    @0
    csup
    cB
    cA
    cR
    cinf
    cC
    cA
    cR
    cinf
    cA
    cB
    cC
    @0
    supeq1
    cB
    cA
    cR
    df-inf
    cC
    cA
    cR
    df-inf
    3eqtr4g
end
