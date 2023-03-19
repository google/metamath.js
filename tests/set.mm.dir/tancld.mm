include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "ctan.mm"
include "tancl.mm"
include "syl2anc.mm"

theorem tancld
  let wph: wff ph
  let cA: class A
  assume sincld.1: |- ( ph -> A e. CC )
  assume tancld.2: |- ( ph -> ( cos ` A ) =/= 0 )


  assert |- ( ph -> ( tan ` A ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    ccos
    cfv
    cc0
    wne
    cA
    ctan
    cfv
    cc
    wcel
    sincld.1
    tancld.2
    cA
    tancl
    syl2anc
end
