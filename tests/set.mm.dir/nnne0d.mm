include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "syl.mm"

theorem nnne0d
  let wph: wff ph
  let cA: class A
  assume nnge1d.1: |- ( ph -> A e. NN )


  assert |- ( ph -> A =/= 0 )

  proof
    wph
    cA
    cn
    wcel
    cA
    cc0
    wne
    nnge1d.1
    cA
    nnne0
    syl
end
