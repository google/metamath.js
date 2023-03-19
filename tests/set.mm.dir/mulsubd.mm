include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "mulsub.mm"
include "syl22anc.mm"

theorem mulsubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mulm1d.1: |- ( ph -> A e. CC )
  assume mulnegd.2: |- ( ph -> B e. CC )
  assume subdid.3: |- ( ph -> C e. CC )
  assume muladdd.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( A - B ) x. ( C - D ) ) = ( ( ( A x. C ) + ( D x. B ) ) - ( ( A x. D ) + ( C x. B ) ) ) )

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
    cmin
    co
    cC
    cD
    cmin
    co
    cmul
    co
    cA
    cC
    cmul
    co
    cD
    cB
    cmul
    co
    caddc
    co
    cA
    cD
    cmul
    co
    cC
    cB
    cmul
    co
    caddc
    co
    cmin
    co
    wceq
    mulm1d.1
    mulnegd.2
    subdid.3
    muladdd.4
    cA
    cB
    cC
    cD
    mulsub
    syl22anc
end
