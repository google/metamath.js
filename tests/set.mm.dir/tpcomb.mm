include "ctp.mm"
include "tpcoma.mm"
include "tprot.mm"
include "3eqtr4i.mm"

theorem tpcomb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { A , B , C } = { A , C , B }

  proof
    cB
    cC
    cA
    ctp
    cC
    cB
    cA
    ctp
    cA
    cB
    cC
    ctp
    cA
    cC
    cB
    ctp
    cB
    cC
    cA
    tpcoma
    cA
    cB
    cC
    tprot
    cA
    cC
    cB
    tprot
    3eqtr4i
end
