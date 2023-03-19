include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "recn.mm"
include "syl.mm"

theorem recnd
  let wph: wff ph
  let cA: class A
  assume recnd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A e. CC )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc
    wcel
    recnd.1
    cA
    recn
    syl
end
