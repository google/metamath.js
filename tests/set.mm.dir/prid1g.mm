include "wcel.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "orci.mm"
include "elprg.mm"
include "mpbiri.mm"

theorem prid1g
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> A e. { A , B } )

  proof
    cA
    cV
    wcel
    cA
    cA
    cB
    cpr
    wcel
    cA
    cA
    wceq
    #
    cA
    cB
    wceq
    #
    wo
    @0
    @1
    cA
    eqid
    orci
    cA
    cA
    cB
    cV
    elprg
    mpbiri
end
