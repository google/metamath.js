include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mul12.mm"
include "syl3anc.mm"

theorem mul12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A x. ( B x. C ) ) = ( B x. ( A x. C ) ) )

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
    cmul
    co
    cmul
    co
    cB
    cA
    cC
    cmul
    co
    cmul
    co
    wceq
    muld.1
    addcomd.2
    addcand.3
    cA
    cB
    cC
    mul12
    syl3anc
end
