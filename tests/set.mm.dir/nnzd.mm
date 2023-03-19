include "nnnn0d.mm"
include "nn0zd.mm"

theorem nnzd
  let wph: wff ph
  let cA: class A
  assume nnzd.1: |- ( ph -> A e. NN )


  assert |- ( ph -> A e. ZZ )

  proof
    wph
    cA
    wph
    cA
    nnzd.1
    nnnn0d
    nn0zd
end
