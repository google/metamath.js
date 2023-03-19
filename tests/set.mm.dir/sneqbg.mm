include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "sneqrg.mm"
include "sneq.mm"
include "impbid1.mm"

theorem sneqbg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( { A } = { B } <-> A = B ) )

  proof
    cA
    cV
    wcel
    cA
    csn
    cB
    csn
    wceq
    cA
    cB
    wceq
    cA
    cB
    cV
    sneqrg
    cA
    cB
    sneq
    impbid1
end
