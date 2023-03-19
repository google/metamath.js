include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "wceq.mm"
include "negneg.mm"
include "syl.mm"

theorem negnegd
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )


  assert |- ( ph -> -u -u A = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    cneg
    cneg
    cA
    wceq
    negidd.1
    cA
    negneg
    syl
end
