include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "muladd.mm"
include "mp4an.mm"

theorem muladdi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mulm1.1: |- A e. CC
  assume mulneg.2: |- B e. CC
  assume subdi.3: |- C e. CC
  assume muladdi.4: |- D e. CC


  assert |- ( ( A + B ) x. ( C + D ) ) = ( ( ( A x. C ) + ( D x. B ) ) + ( ( A x. D ) + ( C x. B ) ) )

  proof
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
    mulm1.1
    mulneg.2
    subdi.3
    muladdi.4
    cA
    cB
    cC
    cD
    muladd
    mp4an
end
