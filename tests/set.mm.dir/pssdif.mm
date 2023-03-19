include "wpss.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "cdif.mm"
include "c0.mm"
include "df-pss.mm"
include "pssdifn0.mm"
include "sylbi.mm"

theorem pssdif
  let cA: class A
  let cB: class B


  assert |- ( A C. B -> ( B \ A ) =/= (/) )

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
    wa
    cB
    cA
    cdif
    c0
    wne
    cA
    cB
    df-pss
    cA
    cB
    pssdifn0
    sylbi
end
