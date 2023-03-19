include "syl5eq.mm"
include "eqcomd.mm"

theorem syl5req
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5req.1: |- A = B
  assume syl5req.2: |- ( ph -> B = C )


  assert |- ( ph -> C = A )

  proof
    wph
    cA
    cC
    wph
    cA
    cB
    cC
    syl5req.1
    syl5req.2
    syl5eq
    eqcomd
end
