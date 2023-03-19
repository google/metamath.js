include "cn0.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "nn0nepnf.mm"
include "syl.mm"

theorem nn0nepnfd
  let wph: wff ph
  let cA: class A
  assume nn0xnn0d.1: |- ( ph -> A e. NN0 )


  assert |- ( ph -> A =/= +oo )

  proof
    wph
    cA
    cn0
    wcel
    cA
    cpnf
    wne
    nn0xnn0d.1
    cA
    nn0nepnf
    syl
end
