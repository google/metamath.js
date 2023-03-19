include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cr.mm"
include "nnrecre.mm"
include "syl.mm"

theorem nnrecred
  let wph: wff ph
  let cA: class A
  assume nnge1d.1: |- ( ph -> A e. NN )


  assert |- ( ph -> ( 1 / A ) e. RR )

  proof
    wph
    cA
    cn
    wcel
    c1
    cA
    cdiv
    co
    cr
    wcel
    nnge1d.1
    cA
    nnrecre
    syl
end
