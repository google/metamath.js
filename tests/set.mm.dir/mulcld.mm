include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "mulcl.mm"
include "syl2anc.mm"

theorem mulcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume addcld.1: |- ( ph -> A e. CC )
  assume addcld.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A x. B ) e. CC )

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
    cmul
    co
    cc
    wcel
    addcld.1
    addcld.2
    cA
    cB
    mulcl
    syl2anc
end
