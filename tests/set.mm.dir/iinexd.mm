include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "wral.mm"
include "ciin.mm"
include "cvv.mm"
include "iinexg.mm"
include "syl2anc.mm"

theorem iinexd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume iinexd.1: |- ( ph -> A =/= (/) )
  assume iinexd.2: |- ( ph -> A. x e. A B e. C )

  disjoint A x
  assert |- ( ph -> |^|_ x e. A B e. _V )

  proof
    wph
    cA
    c0
    wne
    cB
    cC
    wcel
    vx
    cA
    wral
    vx
    cA
    cB
    ciin
    cvv
    wcel
    iinexd.1
    iinexd.2
    vx
    cA
    cB
    cC
    iinexg
    syl2anc
end
