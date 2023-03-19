include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "negcl.mm"
include "syl.mm"

theorem negcld
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> -u A e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    cneg
    cc
    wcel
    negidd.1
    cA
    negcl
    syl
end
