include "eqcomd.mm"
include "syl5breq.mm"

theorem syl5breqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl5breqr.1: |- A R B
  assume syl5breqr.2: |- ( ph -> C = B )


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cC
    cR
    syl5breqr.1
    wph
    cC
    cB
    syl5breqr.2
    eqcomd
    syl5breq
end
