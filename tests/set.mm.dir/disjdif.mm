include "cin.mm"
include "wss.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "inss1.mm"
include "inssdif0.mm"
include "mpbi.mm"

theorem disjdif
  let cA: class A
  let cB: class B


  assert |- ( A i^i ( B \ A ) ) = (/)

  proof
    cA
    cB
    cin
    cA
    wss
    cA
    cB
    cA
    cdif
    cin
    c0
    wceq
    cA
    cB
    inss1
    cA
    cB
    cA
    inssdif0
    mpbi
end
