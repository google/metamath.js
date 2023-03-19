include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "breq12.mm"
include "mp2an.mm"

theorem breq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume breq1i.1: |- A = B
  assume breq12i.2: |- C = D


  assert |- ( A R C <-> B R D )

  proof
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
    breq1i.1
    breq12i.2
    cA
    cB
    cC
    cD
    cR
    breq12
    mp2an
end
