include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"

theorem elexd
  let wph: wff ph
  let cA: class A
  let cV: class V
  assume elexd.1: |- ( ph -> A e. V )


  assert |- ( ph -> A e. _V )

  proof
    wph
    cA
    cV
    wcel
    cA
    cvv
    wcel
    elexd.1
    cA
    cV
    elex
    syl
end
