include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq12.mm"
include "syl2anc.mm"

theorem breq12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume breq1d.1: |- ( ph -> A = B )
  assume breq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> ( A R C <-> B R D ) )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cR
    wbr
    cB
    cD
    cR
    wbr
    wb
    breq1d.1
    breq12d.2
    cA
    cB
    cC
    cD
    cR
    breq12
    syl2anc
end
