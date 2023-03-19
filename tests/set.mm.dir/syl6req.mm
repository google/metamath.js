include "syl6eq.mm"
include "eqcomd.mm"

theorem syl6req
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume syl6req.1: |- ( ph -> A = B )
  assume syl6req.2: |- B = C


  assert |- ( ph -> C = A )

  proof
    wph
    cA
    cC
    wph
    cA
    cB
    cC
    syl6req.1
    syl6req.2
    syl6eq
    eqcomd
end
