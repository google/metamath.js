include "cn.mm"
include "cn0.mm"
include "nnssnn0.mm"
include "sseldi.mm"

theorem nnnn0d
  let wph: wff ph
  let cA: class A
  assume nnnn0d.1: |- ( ph -> A e. NN )


  assert |- ( ph -> A e. NN0 )

  proof
    wph
    cn
    cn0
    cA
    nnssnn0
    nnnn0d.1
    sseldi
end
