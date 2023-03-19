include "cn.mm"
include "wcel.mm"
include "crp.mm"
include "nnrp.mm"
include "syl.mm"

theorem nnrpd
  let wph: wff ph
  let cA: class A
  assume nnrpd.1: |- ( ph -> A e. NN )


  assert |- ( ph -> A e. RR+ )

  proof
    wph
    cA
    cn
    wcel
    cA
    crp
    wcel
    nnrpd.1
    cA
    nnrp
    syl
end
