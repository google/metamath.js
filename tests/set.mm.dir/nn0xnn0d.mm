include "cn0.mm"
include "cxnn0.mm"
include "nn0ssxnn0.mm"
include "sseldi.mm"

theorem nn0xnn0d
  let wph: wff ph
  let cA: class A
  assume nn0xnn0d.1: |- ( ph -> A e. NN0 )


  assert |- ( ph -> A e. NN0* )

  proof
    wph
    cn0
    cxnn0
    cA
    nn0ssxnn0
    nn0xnn0d.1
    sseldi
end
