include "con0.mm"
include "wcel.mm"
include "word.mm"
include "csuc.mm"
include "wa.mm"
include "wn.mm"
include "eloni.mm"
include "ordnbtwn.mm"
include "syl.mm"

theorem onnbtwn
  let cA: class A
  let cB: class B


  assert |- ( A e. On -> -. ( A e. B /\ B e. suc A ) )

  proof
    cA
    con0
    wcel
    cA
    word
    cA
    cB
    wcel
    cB
    cA
    csuc
    wcel
    wa
    wn
    cA
    eloni
    cA
    cB
    ordnbtwn
    syl
end
