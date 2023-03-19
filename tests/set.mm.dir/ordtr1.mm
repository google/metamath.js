include "word.mm"
include "wtr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ordtr.mm"
include "trel.mm"
include "syl.mm"

theorem ordtr1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( Ord C -> ( ( A e. B /\ B e. C ) -> A e. C ) )

  proof
    cC
    word
    cC
    wtr
    cA
    cB
    wcel
    cB
    cC
    wcel
    wa
    cA
    cC
    wcel
    wi
    cC
    ordtr
    cC
    cA
    cB
    trel
    syl
end
