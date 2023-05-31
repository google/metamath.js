include "eqcomi.mm"
include "syl6req.mm"

theorem syl6reqr
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume syl6reqr.1: |- ( ph -> A = B )
  assume syl6reqr.2: |- C = B


  assert |- ( ph -> C = A )

  proof
    wph
    cA
    cB
    cC
    syl6reqr.1
    cC
    cB
    syl6reqr.2
    eqcomi
    syl6req
end
