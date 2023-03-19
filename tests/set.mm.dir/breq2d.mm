include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq2.mm"
include "syl.mm"

theorem breq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume breq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( C R A <-> C R B ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cA
    cR
    wbr
    cC
    cB
    cR
    wbr
    wb
    breq1d.1
    cA
    cB
    cC
    cR
    breq2
    syl
end
