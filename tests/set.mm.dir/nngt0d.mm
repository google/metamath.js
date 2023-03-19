include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "nngt0.mm"
include "syl.mm"

theorem nngt0d
  let wph: wff ph
  let cA: class A
  assume nnge1d.1: |- ( ph -> A e. NN )


  assert |- ( ph -> 0 < A )

  proof
    wph
    cA
    cn
    wcel
    cc0
    cA
    clt
    wbr
    nnge1d.1
    cA
    nngt0
    syl
end
