include "wcel.mm"
include "cres.mm"
include "cvv.mm"
include "resexg.mm"
include "syl.mm"

theorem resexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  assume resexd.1: |- ( ph -> A e. V )


  assert |- ( ph -> ( A |` B ) e. _V )

  proof
    wph
    cA
    cV
    wcel
    cA
    cB
    cres
    cvv
    wcel
    resexd.1
    cA
    cB
    cV
    resexg
    syl
end
