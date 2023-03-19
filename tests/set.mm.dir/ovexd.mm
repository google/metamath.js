include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "a1i.mm"

theorem ovexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ph -> ( A F B ) e. _V )

  proof
    cA
    cB
    cF
    co
    cvv
    wcel
    wph
    cA
    cB
    cF
    ovex
    a1i
end
