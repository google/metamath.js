include "cc.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "efcl.mm"
include "syl.mm"

theorem efcld
  let wph: wff ph
  let cA: class A
  assume efcld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( exp ` A ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    ce
    cfv
    cc
    wcel
    efcld.1
    cA
    efcl
    syl
end
