include "cres.mm"
include "reseq1i.mm"
include "reseq2i.mm"
include "eqtri.mm"

theorem reseq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume reseqi.1: |- A = B
  assume reseqi.2: |- C = D


  assert |- ( A |` C ) = ( B |` D )

  proof
    cA
    cC
    cres
    cB
    cC
    cres
    cB
    cD
    cres
    cA
    cB
    cC
    reseqi.1
    reseq1i
    cC
    cD
    cB
    reseqi.2
    reseq2i
    eqtri
end
