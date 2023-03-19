include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addsub.mm"
include "syl3anc.mm"

theorem addsubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + B ) - C ) = ( ( A - C ) + B ) )

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
    cC
    cmin
    co
    cB
    caddc
    co
    wceq
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    addsub
    syl3anc
end
