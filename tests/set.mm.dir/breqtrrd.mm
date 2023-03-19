include "eqcomd.mm"
include "breqtrd.mm"

theorem breqtrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breqtrrd.1: |- ( ph -> A R B )
  assume breqtrrd.2: |- ( ph -> C = B )


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cC
    cR
    breqtrrd.1
    wph
    cC
    cB
    breqtrrd.2
    eqcomd
    breqtrd
end
