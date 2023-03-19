include "word.mm"
include "cep.mm"
include "wwe.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "ordwe.mm"
include "wefrc.mm"
include "syl3an1.mm"

theorem tz7.5
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint B x
  assert |- ( ( Ord A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) )

  proof
    cA
    word
    cA
    cep
    wwe
    cB
    cA
    wss
    cB
    c0
    wne
    cB
    vx
    cv
    cin
    c0
    wceq
    vx
    cB
    wrex
    cA
    ordwe
    vx
    cA
    cB
    wefrc
    syl3an1
end
