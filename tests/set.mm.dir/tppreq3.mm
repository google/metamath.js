include "wceq.mm"
include "ctp.mm"
include "cpr.mm"
include "tpeq3.mm"
include "eqcoms.mm"
include "tpidm23.mm"
include "syl6eq.mm"

theorem tppreq3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( B = C -> { A , B , C } = { A , B } )

  proof
    cB
    cC
    wceq
    cA
    cB
    cC
    ctp
    #
    cA
    cB
    cB
    ctp
    #
    cA
    cB
    cpr
    @0
    @1
    wceq
    cC
    cB
    cC
    cB
    cA
    cB
    tpeq3
    eqcoms
    cA
    cB
    tpidm23
    syl6eq
end
