include "wcel.mm"
include "sseld.mm"
include "imp.mm"

theorem sselda
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseld.1: |- ( ph -> A C_ B )


  assert |- ( ( ph /\ C e. A ) -> C e. B )

  proof
    wph
    cC
    cA
    wcel
    cC
    cB
    wcel
    wph
    cA
    cB
    cC
    sseld.1
    sseld
    imp
end
