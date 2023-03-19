include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "adddi.mm"
include "syl3anc.mm"

theorem adddid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addcld.1: |- ( ph -> A e. CC )
  assume addcld.2: |- ( ph -> B e. CC )
  assume addassd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A x. ( B + C ) ) = ( ( A x. B ) + ( A x. C ) ) )

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
    cC
    caddc
    co
    cmul
    co
    cA
    cB
    cmul
    co
    cA
    cC
    cmul
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
    adddi
    syl3anc
end
