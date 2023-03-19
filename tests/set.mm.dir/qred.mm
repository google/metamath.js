include "cq.mm"
include "wcel.mm"
include "cr.mm"
include "qre.mm"
include "syl.mm"

theorem qred
  let wph: wff ph
  let cA: class A
  assume qred.1: |- ( ph -> A e. QQ )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    cq
    wcel
    cA
    cr
    wcel
    qred.1
    cA
    qre
    syl
end
