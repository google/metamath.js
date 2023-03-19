include "wss.mm"
include "cin.mm"
include "ssrin.mm"
include "syl.mm"

theorem ssrind
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssrind.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( A i^i C ) C_ ( B i^i C ) )

  proof
    wph
    cA
    cB
    wss
    cA
    cC
    cin
    cB
    cC
    cin
    wss
    ssrind.1
    cA
    cB
    cC
    ssrin
    syl
end
