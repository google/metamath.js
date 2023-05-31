include "eqcomi.mm"
include "syl6eq.mm"

theorem syl6eqr
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume syl6eqr.1: |- ( ph -> A = B )
  assume syl6eqr.2: |- C = B


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cB
    cC
    syl6eqr.1
    cC
    cB
    syl6eqr.2
    eqcomi
    syl6eq
end
