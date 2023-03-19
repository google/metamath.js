include "cn0.mm"
include "cr.mm"
include "nn0ssre.mm"
include "sseldi.mm"

theorem nn0red
  let wph: wff ph
  let cA: class A
  assume nn0red.1: |- ( ph -> A e. NN0 )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cn0
    cr
    cA
    nn0ssre
    nn0red.1
    sseldi
end
