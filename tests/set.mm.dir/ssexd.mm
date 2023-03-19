include "wss.mm"
include "wcel.mm"
include "cvv.mm"
include "ssexg.mm"
include "syl2anc.mm"

theorem ssexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssexd.1: |- ( ph -> B e. C )
  assume ssexd.2: |- ( ph -> A C_ B )


  assert |- ( ph -> A e. _V )

  proof
    wph
    cA
    cB
    wss
    cB
    cC
    wcel
    cA
    cvv
    wcel
    ssexd.2
    ssexd.1
    cA
    cB
    cC
    ssexg
    syl2anc
end
