include "eqcomd.mm"
include "eqtrd.mm"

theorem eqtr4d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
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
