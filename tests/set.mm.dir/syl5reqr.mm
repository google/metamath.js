include "eqcomi.mm"
include "syl5req.mm"

theorem syl5reqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5reqr.1: |- B = A
  assume syl5reqr.2: |- ( ph -> B = C )


  assert |- ( ph -> C = A )

  proof
    wph
    cA
    cB
    cC
    cB
    cA
    syl5reqr.1
    eqcomi
    syl5reqr.2
    syl5req
end
