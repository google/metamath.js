include "cn.mm"
include "cc.mm"
include "nnsscn.mm"
include "sseldi.mm"

theorem nncnd
  let wph: wff ph
  let cA: class A
  assume nnred.1: |- ( ph -> A e. NN )


  assert |- ( ph -> A e. CC )

  proof
    wph
    cn
    cc
    cA
    nnsscn
    nnred.1
    sseldi
end
