include "wfn.mm"
include "wfun.mm"
include "fnfun.mm"
include "syl.mm"

theorem bnj930
  let wph: wff ph
  let cA: class A
  let cF: class F
  assume bnj930.1: |- ( ph -> F Fn A )


  assert |- ( ph -> Fun F )

  proof
    wph
    cF
    cA
    wfn
    cF
    wfun
    bnj930.1
    cA
    cF
    fnfun
    syl
end
