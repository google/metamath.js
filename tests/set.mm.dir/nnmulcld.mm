include "cn.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "nnmulcl.mm"
include "syl2anc.mm"

theorem nnmulcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume nnge1d.1: |- ( ph -> A e. NN )
  assume nnmulcld.2: |- ( ph -> B e. NN )


  assert |- ( ph -> ( A x. B ) e. NN )

  proof
    wph
    cA
    cn
    wcel
    cB
    cn
    wcel
    cA
    cB
    cmul
    co
    cn
    wcel
    nnge1d.1
    nnmulcld.2
    cA
    cB
    nnmulcl
    syl2anc
end
