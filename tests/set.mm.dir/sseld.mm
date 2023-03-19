include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "ssel.mm"
include "syl.mm"

theorem sseld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseld.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( C e. A -> C e. B ) )

  proof
    wph
    cA
    cB
    wss
    cC
    cA
    wcel
    cC
    cB
    wcel
    wi
    sseld.1
    cA
    cB
    cC
    ssel
    syl
end
