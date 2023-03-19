include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "2addsub.mm"
include "syl22anc.mm"

theorem 2addsubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )
  assume addsub4d.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( ( A + B ) + C ) - D ) = ( ( ( A + C ) - D ) + B ) )

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
    cD
    cc
    wcel
    cA
    cB
    caddc
    co
    cC
    caddc
    co
    cD
    cmin
    co
    cA
    cC
    caddc
    co
    cD
    cmin
    co
    cB
    caddc
    co
    wceq
    negidd.1
    pncand.2
    subaddd.3
    addsub4d.4
    cA
    cB
    cC
    cD
    2addsub
    syl22anc
end
