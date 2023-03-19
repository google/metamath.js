include "wcel.mm"
include "sseld.mm"
include "con3d.mm"

theorem ssneld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ssneld.1: |- ( ph -> A C_ B )


  assert |- ( ph -> ( -. C e. B -> -. C e. A ) )

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
    ssneld.1
    sseld
    con3d
end
