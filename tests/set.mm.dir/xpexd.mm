include "wcel.mm"
include "cxp.mm"
include "cvv.mm"
include "xpexg.mm"
include "syl2anc.mm"

theorem xpexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume xpexd.1: |- ( ph -> A e. V )
  assume xpexd.2: |- ( ph -> B e. W )


  assert |- ( ph -> ( A X. B ) e. _V )

  proof
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    cA
    cB
    cxp
    cvv
    wcel
    xpexd.1
    xpexd.2
    cA
    cB
    cV
    cW
    xpexg
    syl2anc
end
