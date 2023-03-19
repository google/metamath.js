include "wf.mm"
include "wcel.mm"
include "cvv.mm"
include "fex.mm"
include "syl2anc.mm"

theorem fexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  assume fexd.1: |- ( ph -> F : A --> B )
  assume fexd.2: |- ( ph -> A e. C )


  assert |- ( ph -> F e. _V )

  proof
    wph
    cA
    cB
    cF
    wf
    cA
    cC
    wcel
    cF
    cvv
    wcel
    fexd.1
    fexd.2
    cA
    cB
    cC
    cF
    fex
    syl2anc
end
