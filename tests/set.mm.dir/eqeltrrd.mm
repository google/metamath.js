include "eqcomd.mm"
include "eqeltrd.mm"

theorem eqeltrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqeltrrd.1: |- ( ph -> A = B )
  assume eqeltrrd.2: |- ( ph -> A e. C )


  assert |- ( ph -> B e. C )

  proof
    wph
    cB
    cA
    cC
    wph
    cA
    cB
    eqeltrrd.1
    eqcomd
    eqeltrrd.2
    eqeltrd
end
