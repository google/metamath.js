include "eqcomi.mm"
include "syl6breq.mm"

theorem syl6breqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl6breqr.1: |- ( ph -> A R B )
  assume syl6breqr.2: |- C = B


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cC
    cR
    syl6breqr.1
    cC
    cB
    syl6breqr.2
    eqcomi
    syl6breq
end
