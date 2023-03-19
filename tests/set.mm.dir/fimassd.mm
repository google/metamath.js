include "wf.mm"
include "cima.mm"
include "wss.mm"
include "fimass.mm"
include "syl.mm"

theorem fimassd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  assume fimassd.1: |- ( ph -> F : A --> B )


  assert |- ( ph -> ( F " X ) C_ B )

  proof
    wph
    cA
    cB
    cF
    wf
    cF
    cX
    cima
    cB
    wss
    fimassd.1
    cA
    cB
    cF
    cX
    fimass
    syl
end
