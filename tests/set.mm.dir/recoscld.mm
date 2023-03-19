include "cr.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "recoscl.mm"
include "syl.mm"

theorem recoscld
  let wph: wff ph
  let cA: class A
  assume resincld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( cos ` A ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    ccos
    cfv
    cr
    wcel
    resincld.1
    cA
    recoscl
    syl
end
