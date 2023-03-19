include "wcel.mm"
include "eleq1d.mm"
include "mtbird.mm"

theorem eqneltrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqneltrd.1: |- ( ph -> A = B )
  assume eqneltrd.2: |- ( ph -> -. B e. C )


  assert |- ( ph -> -. A e. C )

  proof
    wph
    cA
    cC
    wcel
    cB
    cC
    wcel
    eqneltrd.2
    wph
    cA
    cB
    cC
    eqneltrd.1
    eleq1d
    mtbird
end
