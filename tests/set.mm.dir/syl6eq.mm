include "wceq.mm"
include "a1i.mm"
include "eqtrd.mm"

theorem syl6eq
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume syl6eq.1: |- ( ph -> A = B )
  assume syl6eq.2: |- B = C


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cB
    cC
    syl6eq.1
    cB
    cC
    wceq
    wph
    syl6eq.2
    a1i
    eqtrd
end
