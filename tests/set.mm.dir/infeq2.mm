include "wceq.mm"
include "ccnv.mm"
include "csup.mm"
include "cinf.mm"
include "supeq2.mm"
include "df-inf.mm"
include "3eqtr4g.mm"

theorem infeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( B = C -> inf ( A , B , R ) = inf ( A , C , R ) )

  proof
    cB
    cC
    wceq
    cA
    cB
    cR
    ccnv
    #
    csup
    cA
    cC
    @0
    csup
    cA
    cB
    cR
    cinf
    cA
    cC
    cR
    cinf
    cA
    cB
    cC
    @0
    supeq2
    cA
    cB
    cR
    df-inf
    cA
    cC
    cR
    df-inf
    3eqtr4g
end
