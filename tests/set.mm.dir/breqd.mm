include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq.mm"
include "syl.mm"

theorem breqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume breq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C A D <-> C B D ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    cA
    wbr
    cC
    cD
    cB
    wbr
    wb
    breq1d.1
    cC
    cD
    cA
    cB
    breq
    syl
end
