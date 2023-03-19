include "wcel.mm"
include "cpw.mm"
include "cvv.mm"
include "pwexg.mm"
include "syl.mm"

theorem pwexd
  let wph: wff ph
  let cA: class A
  let cV: class V
  assume pwexd.1: |- ( ph -> A e. V )


  assert |- ( ph -> ~P A e. _V )

  proof
    wph
    cA
    cV
    wcel
    cA
    cpw
    cvv
    wcel
    pwexd.1
    cA
    cV
    pwexg
    syl
end
