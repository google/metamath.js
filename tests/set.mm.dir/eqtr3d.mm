include "eqcomd.mm"
include "eqtrd.mm"

theorem eqtr3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqtr3d.1: |- ( ph -> A = B )
  assume eqtr3d.2: |- ( ph -> A = C )


  assert |- ( ph -> B = C )

  proof
    wph
    cB
    cA
    cC
    wph
    cA
    cB
    eqtr3d.1
    eqcomd
    eqtr3d.2
    eqtrd
end
