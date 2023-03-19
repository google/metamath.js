include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "df-pss.mm"
include "simplbi.mm"

theorem pssss
  let cA: class A
  let cB: class B


  assert |- ( A C. B -> A C_ B )

  proof
    cA
    cB
    wpss
    cA
    cB
    wss
    cA
    cB
    wne
    cA
    cB
    df-pss
    simplbi
end
