include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul31.mm"
include "syl3anc.mm"

theorem mul31d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A x. B ) x. C ) = ( ( C x. B ) x. A ) )

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
    cC
    cB
    cmul
    co
    cA
    cmul
    co
    wceq
    muld.1
    addcomd.2
    addcand.3
    cA
    cB
    cC
    mul31
    syl3anc
end
