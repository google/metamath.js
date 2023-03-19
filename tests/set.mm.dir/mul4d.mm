include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul4.mm"
include "syl22anc.mm"

theorem mul4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )
  assume mul4d.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( A x. B ) x. ( C x. D ) ) = ( ( A x. C ) x. ( B x. D ) ) )

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
    cmul
    co
    cC
    cD
    cmul
    co
    cmul
    co
    cA
    cC
    cmul
    co
    cB
    cD
    cmul
    co
    cmul
    co
    wceq
    muld.1
    addcomd.2
    addcand.3
    mul4d.4
    cA
    cB
    cC
    cD
    mul4
    syl22anc
end
