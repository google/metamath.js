include "wcel.mm"
include "sseli.mm"
include "syl.mm"

theorem sseldi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume sseli.1: |- A C_ B
  assume sseldi.2: |- ( ph -> C e. A )


  assert |- ( ph -> C e. B )

  proof
    wph
    cC
    cA
    wcel
    cC
    cB
    wcel
    sseldi.2
    cA
    cB
    cC
    sseli.1
    sseli
    syl
end
