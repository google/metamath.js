include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addsubass.mm"
include "syl3anc.mm"

theorem addsubassd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + B ) - C ) = ( A + ( B - C ) ) )

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
    cmin
    co
    cA
    cB
    cC
    cmin
    co
    caddc
    co
    wceq
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    addsubass
    syl3anc
end
