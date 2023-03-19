include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "nnge1.mm"
include "syl.mm"

theorem nnge1d
  let wph: wff ph
  let cA: class A
  assume nnge1d.1: |- ( ph -> A e. NN )


  assert |- ( ph -> 1 <_ A )

  proof
    wph
    cA
    cn
    wcel
    c1
    cA
    cle
    wbr
    nnge1d.1
    cA
    nnge1
    syl
end
