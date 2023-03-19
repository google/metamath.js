include "cn0.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "nn0mulcl.mm"
include "syl2anc.mm"

theorem nn0mulcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume nn0red.1: |- ( ph -> A e. NN0 )
  assume nn0addcld.2: |- ( ph -> B e. NN0 )


  assert |- ( ph -> ( A x. B ) e. NN0 )

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
    cmul
    co
    cn0
    wcel
    nn0red.1
    nn0addcld.2
    cA
    cB
    nn0mulcl
    syl2anc
end
