include "wcel.mm"
include "eleq1d.mm"
include "mpbird.mm"

theorem eqeltrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqeltrd.1: |- ( ph -> A = B )
  assume eqeltrd.2: |- ( ph -> B e. C )


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cC
    wcel
    cB
    cC
    wcel
    eqeltrd.2
    wph
    cA
    cB
    cC
    eqeltrd.1
    eleq1d
    mpbird
end
