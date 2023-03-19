include "nn0red.mm"
include "recnd.mm"

theorem nn0cnd
  let wph: wff ph
  let cA: class A
  assume nn0red.1: |- ( ph -> A e. NN0 )


  assert |- ( ph -> A e. CC )

  proof
    wph
    cA
    wph
    cA
    nn0red.1
    nn0red
    recnd
end
