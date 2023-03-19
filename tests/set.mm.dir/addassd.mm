include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addass.mm"
include "syl3anc.mm"

theorem addassd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addcld.1: |- ( ph -> A e. CC )
  assume addcld.2: |- ( ph -> B e. CC )
  assume addassd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + B ) + C ) = ( A + ( B + C ) ) )

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
    caddc
    co
    cC
    caddc
    co
    cA
    cB
    cC
    caddc
    co
    caddc
    co
    wceq
    addcld.1
    addcld.2
    addassd.3
    cA
    cB
    cC
    addass
    syl3anc
end
