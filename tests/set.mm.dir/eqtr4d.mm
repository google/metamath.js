include "eqcomd.mm"
include "eqtrd.mm"

theorem eqtr4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqtr4d.1: |- ( ph -> A = B )
  assume eqtr4d.2: |- ( ph -> C = B )


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cB
    cC
    eqtr4d.1
    wph
    cC
    cB
    eqtr4d.2
    eqcomd
    eqtrd
end
