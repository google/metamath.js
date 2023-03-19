include "cn0.mm"
include "cz.mm"
include "nn0ssz.mm"
include "sseldi.mm"

theorem nn0zd
  let wph: wff ph
  let cA: class A
  assume nn0zd.1: |- ( ph -> A e. NN0 )


  assert |- ( ph -> A e. ZZ )

  proof
    wph
    cn0
    cz
    cA
    nn0ssz
    nn0zd.1
    sseldi
end
