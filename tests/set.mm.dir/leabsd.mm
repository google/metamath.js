include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "leabs.mm"
include "syl.mm"

theorem leabsd
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A <_ ( abs ` A ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cA
    cabs
    cfv
    cle
    wbr
    resqrcld.1
    cA
    leabs
    syl
end
