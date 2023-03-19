include "wcel.mm"
include "cfv.mm"
include "ffvelrnda.mm"
include "mpdan.mm"

theorem ffvelrnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume ffvelrnd.1: |- ( ph -> F : A --> B )
  assume ffvelrnd.2: |- ( ph -> C e. A )


  assert |- ( ph -> ( F ` C ) e. B )

  proof
    wph
    cC
    cA
    wcel
    cC
    cF
    cfv
    cB
    wcel
    ffvelrnd.2
    wph
    cA
    cB
    cC
    cF
    ffvelrnd.1
    ffvelrnda
    mpdan
end
