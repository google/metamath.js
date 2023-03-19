include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0.mm"
include "syl.mm"

theorem nn0ge0d
  let wph: wff ph
  let cA: class A
  assume nn0red.1: |- ( ph -> A e. NN0 )


  assert |- ( ph -> 0 <_ A )

  proof
    wph
    cA
    cn0
    wcel
    cc0
    cA
    cle
    wbr
    nn0red.1
    cA
    nn0ge0
    syl
end
