include "wcel.mm"
include "cmpt.mm"
include "cvv.mm"
include "mptexg.mm"
include "syl.mm"

theorem mptexd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume mptexd.1: |- ( ph -> A e. V )

  disjoint A x
  assert |- ( ph -> ( x e. A |-> B ) e. _V )

  proof
    wph
    cA
    cV
    wcel
    vx
    cA
    cB
    cmpt
    cvv
    wcel
    mptexd.1
    vx
    cA
    cB
    cV
    mptexg
    syl
end
