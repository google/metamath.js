include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"

theorem ffnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume ffnd.1: |- ( ph -> F : A --> B )


  assert |- ( ph -> F Fn A )

  proof
    wph
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    ffnd.1
    cA
    cB
    cF
    ffn
    syl
end
