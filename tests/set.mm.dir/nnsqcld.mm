include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "nnsqcl.mm"
include "syl.mm"

theorem nnsqcld
  let wph: wff ph
  let cA: class A
  assume nnexpcld.1: |- ( ph -> A e. NN )


  assert |- ( ph -> ( A ^ 2 ) e. NN )

  proof
    wph
    cA
    cn
    wcel
    cA
    c2
    cexp
    co
    cn
    wcel
    nnexpcld.1
    cA
    nnsqcl
    syl
end
