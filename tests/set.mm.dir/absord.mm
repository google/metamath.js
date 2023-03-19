include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "absor.mm"
include "syl.mm"

theorem absord
  let wph: wff ph
  let cA: class A
  assume resqrcld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( ( abs ` A ) = A \/ ( abs ` A ) = -u A ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cabs
    cfv
    #
    cA
    wceq
    @0
    cA
    cneg
    wceq
    wo
    resqrcld.1
    cA
    absor
    syl
end
