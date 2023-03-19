include "cfv.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "breqdi.mm"
include "brne0.mm"
include "fvprc.mm"
include "necon1ai.mm"
include "3syl.mm"

theorem brfvimex
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  assume brfvimex.br: |- ( ph -> A R B )
  assume brfvimex.fv: |- ( ph -> R = ( F ` C ) )


  assert |- ( ph -> C e. _V )

  proof
    wph
    cA
    cB
    cC
    cF
    cfv
    #
    wbr
    @0
    c0
    wne
    cC
    cvv
    wcel
    #
    wph
    cR
    @0
    cA
    cB
    brfvimex.fv
    brfvimex.br
    breqdi
    cA
    cB
    @0
    brne0
    @1
    @0
    c0
    cC
    cF
    fvprc
    necon1ai
    3syl
end
