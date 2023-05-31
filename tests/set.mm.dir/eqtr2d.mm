include "eqtrd.mm"
include "eqcomd.mm"

theorem eqtr2d
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume eqtr2d.1: |- ( ph -> A = B )
  assume eqtr2d.2: |- ( ph -> B = C )


  assert |- ( ph -> C = A )

  proof
    wph
    cA
    cC
    wph
    cA
    cB
    cC
    eqtr2d.1
    eqtr2d.2
    eqtrd
    eqcomd
end
