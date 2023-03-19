include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "muladd.mm"
include "syl22anc.mm"

theorem muladdd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mulm1d.1: |- ( ph -> A e. CC )
  assume mulnegd.2: |- ( ph -> B e. CC )
  assume subdid.3: |- ( ph -> C e. CC )
  assume muladdd.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( A + B ) x. ( C + D ) ) = ( ( ( A x. C ) + ( D x. B ) ) + ( ( A x. D ) + ( C x. B ) ) ) )

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
    cD
    caddc
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
    caddc
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
    muladd
    syl22anc
end
