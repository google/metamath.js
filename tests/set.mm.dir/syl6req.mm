include "syl6eq.mm"
include "eqcomd.mm"

theorem syl6req
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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
