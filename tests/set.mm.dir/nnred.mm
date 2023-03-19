include "cn.mm"
include "cr.mm"
include "nnssre.mm"
include "sseldi.mm"

theorem nnred
  let wph: wff ph
  let cA: class A
  assume nnred.1: |- ( ph -> A e. NN )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cn
    cr
    cA
    nnssre
    nnred.1
    sseldi
end
