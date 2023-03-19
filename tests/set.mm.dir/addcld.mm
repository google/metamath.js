include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "addcl.mm"
include "syl2anc.mm"

theorem addcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume addcld.1: |- ( ph -> A e. CC )
  assume addcld.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A + B ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cc
    wcel
    addcld.1
    addcld.2
    cA
    cB
    addcl
    syl2anc
end
