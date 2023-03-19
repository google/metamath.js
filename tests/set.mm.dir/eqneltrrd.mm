include "eqcomd.mm"
include "eqneltrd.mm"

theorem eqneltrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqneltrrd.1: |- ( ph -> A = B )
  assume eqneltrrd.2: |- ( ph -> -. A e. C )


  assert |- ( ph -> -. B e. C )

  proof
    wph
    cB
    cA
    cC
    wph
    cA
    cB
    eqneltrrd.1
    eqcomd
    eqneltrrd.2
    eqneltrd
end
