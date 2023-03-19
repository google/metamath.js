include "eqtrd.mm"
include "eqcomd.mm"

theorem eqtr2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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
