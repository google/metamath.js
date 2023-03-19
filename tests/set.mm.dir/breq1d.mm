include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq1.mm"
include "syl.mm"

theorem breq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( A R C <-> B R C ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cR
    wbr
    cB
    cC
    cR
    wbr
    wb
    breq1d.1
    cA
    cB
    cC
    cR
    breq1
    syl
end
