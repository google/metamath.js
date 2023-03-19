include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulass.mm"
include "syl3anc.mm"

theorem mulassd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addcld.1: |- ( ph -> A e. CC )
  assume addcld.2: |- ( ph -> B e. CC )
  assume addassd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A x. B ) x. C ) = ( A x. ( B x. C ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    cmul
    co
    cC
    cmul
    co
    cA
    cB
    cC
    cmul
    co
    cmul
    co
    wceq
    addcld.1
    addcld.2
    addassd.3
    cA
    cB
    cC
    mulass
    syl3anc
end
