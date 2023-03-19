include "cdif.mm"
include "difeq1i.mm"
include "difeq2i.mm"
include "eqtri.mm"

theorem difeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume difeq1i.1: |- A = B
  assume difeq12i.2: |- C = D


  assert |- ( A \ C ) = ( B \ D )

  proof
    cA
    cC
    cdif
    cB
    cC
    cdif
    cB
    cD
    cdif
    cA
    cB
    cC
    difeq1i.1
    difeq1i
    cC
    cD
    cB
    difeq12i.2
    difeq2i
    eqtri
end
