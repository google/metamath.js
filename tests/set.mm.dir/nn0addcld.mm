include "cn0.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "nn0addcl.mm"
include "syl2anc.mm"

theorem nn0addcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume nn0red.1: |- ( ph -> A e. NN0 )
  assume nn0addcld.2: |- ( ph -> B e. NN0 )


  assert |- ( ph -> ( A + B ) e. NN0 )

  proof
    wph
    cA
    cn0
    wcel
    cB
    cn0
    wcel
    cA
    cB
    caddc
    co
    cn0
    wcel
    nn0red.1
    nn0addcld.2
    cA
    cB
    nn0addcl
    syl2anc
end
