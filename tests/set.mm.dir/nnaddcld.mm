include "cn.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "nnaddcl.mm"
include "syl2anc.mm"

theorem nnaddcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume nnge1d.1: |- ( ph -> A e. NN )
  assume nnmulcld.2: |- ( ph -> B e. NN )


  assert |- ( ph -> ( A + B ) e. NN )

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
    caddc
    co
    cn
    wcel
    nnge1d.1
    nnmulcld.2
    cA
    cB
    nnaddcl
    syl2anc
end
