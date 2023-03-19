include "wfn.mm"
include "wcel.mm"
include "cvv.mm"
include "fnex.mm"
include "syl2anc.mm"

theorem fnexd
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cV: class V
  assume fnexd.1: |- ( ph -> F Fn A )
  assume fnexd.2: |- ( ph -> A e. V )


  assert |- ( ph -> F e. _V )

  proof
    wph
    cF
    cA
    wfn
    cA
    cV
    wcel
    cF
    cvv
    wcel
    fnexd.1
    fnexd.2
    cA
    cV
    cF
    fnex
    syl2anc
end
