include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "cmo.mm"
include "co.mm"
include "cn0.mm"
include "zmodcl.mm"
include "syl2anc.mm"

theorem zmodcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume zmodcld.1: |- ( ph -> A e. ZZ )
  assume zmodcld.2: |- ( ph -> B e. NN )


  assert |- ( ph -> ( A mod B ) e. NN0 )

  proof
    wph
    cA
    cz
    wcel
    cB
    cn
    wcel
    cA
    cB
    cmo
    co
    cn0
    wcel
    zmodcld.1
    zmodcld.2
    cA
    cB
    zmodcl
    syl2anc
end
