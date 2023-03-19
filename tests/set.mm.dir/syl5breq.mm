include "wbr.mm"
include "a1i.mm"
include "breqtrd.mm"

theorem syl5breq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume syl5breq.1: |- A R B
  assume syl5breq.2: |- ( ph -> B = C )


  assert |- ( ph -> A R C )

  proof
    wph
    cA
    cB
    cC
    cR
    cA
    cB
    cR
    wbr
    wph
    syl5breq.1
    a1i
    syl5breq.2
    breqtrd
end
