include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wss.mm"
include "wne.mm"
include "wpss.mm"
include "ordelssne.mm"
include "df-pss.mm"
include "syl6bbr.mm"

theorem ordelpss
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A e. B <-> A C. B ) )

  proof
    cA
    word
    cB
    word
    wa
    cA
    cB
    wcel
    cA
    cB
    wss
    cA
    cB
    wne
    wa
    cA
    cB
    wpss
    cA
    cB
    ordelssne
    cA
    cB
    df-pss
    syl6bbr
end
