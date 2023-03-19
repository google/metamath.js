include "wceq.mm"
include "wfun.mm"
include "wb.mm"
include "funeq.mm"
include "syl.mm"

theorem funeqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume funeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> ( Fun A <-> Fun B ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    wfun
    cB
    wfun
    wb
    funeqd.1
    cA
    cB
    funeq
    syl
end
