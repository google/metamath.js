include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2nn.mm"
include "syl.mm"

theorem peano2nnd
  let wph: wff ph
  let cA: class A
  assume nnred.1: |- ( ph -> A e. NN )


  assert |- ( ph -> ( A + 1 ) e. NN )

  proof
    wph
    cA
    cn
    wcel
    cA
    c1
    caddc
    co
    cn
    wcel
    nnred.1
    cA
    peano2nn
    syl
end
