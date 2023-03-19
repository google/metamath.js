include "wceq.mm"
include "ccnv.mm"
include "csup.mm"
include "cinf.mm"
include "cnveq.mm"
include "supeq3.mm"
include "syl.mm"
include "df-inf.mm"
include "3eqtr4g.mm"

theorem infeq3
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( R = S -> inf ( A , B , R ) = inf ( A , B , S ) )

  proof
    cR
    cS
    wceq
    #
    cA
    cB
    cR
    ccnv
    #
    csup
    #
    cA
    cB
    cS
    ccnv
    #
    csup
    #
    cA
    cB
    cR
    cinf
    cA
    cB
    cS
    cinf
    @0
    @1
    @3
    wceq
    @2
    @4
    wceq
    cR
    cS
    cnveq
    cA
    cB
    @1
    @3
    supeq3
    syl
    cA
    cB
    cR
    df-inf
    cA
    cB
    cS
    df-inf
    3eqtr4g
end
