include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul32.mm"
include "syl3anc.mm"

theorem mul32d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A x. B ) x. C ) = ( ( A x. C ) x. B ) )

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
    cC
    cmul
    co
    cB
    cmul
    co
    wceq
    muld.1
    addcomd.2
    addcand.3
    cA
    cB
    cC
    mul32
    syl3anc
end
