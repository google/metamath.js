include "nnred.mm"
include "rexrd.mm"

theorem nnxrd
  let wph: wff ph
  let cA: class A
  assume nnxrd.1: |- ( ph -> A e. NN )


  assert |- ( ph -> A e. RR* )

  proof
    wph
    cA
    wph
    cA
    nnxrd.1
    nnred
    rexrd
end
