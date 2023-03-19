include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "leid.mm"
include "syl.mm"

theorem leidd
  let wph: wff ph
  let cA: class A
  assume leidd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A <_ A )

  proof
    wph
    cA
    cr
    wcel
    cA
    cA
    cle
    wbr
    leidd.1
    cA
    leid
    syl
end
