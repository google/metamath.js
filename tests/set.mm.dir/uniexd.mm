include "wcel.mm"
include "cuni.mm"
include "cvv.mm"
include "uniexg.mm"
include "syl.mm"

theorem uniexd
  let wph: wff ph
  let cA: class A
  let cV: class V
  assume uniexd.1: |- ( ph -> A e. V )


  assert |- ( ph -> U. A e. _V )

  proof
    wph
    cA
    cV
    wcel
    cA
    cuni
    cvv
    wcel
    uniexd.1
    cA
    cV
    uniexg
    syl
end
