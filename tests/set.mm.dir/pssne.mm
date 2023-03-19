include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "df-pss.mm"
include "simprbi.mm"

theorem pssne
  let cA: class A
  let cB: class B


  assert |- ( A C. B -> A =/= B )

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
    simprbi
end
