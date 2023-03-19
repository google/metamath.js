include "wpss.mm"
include "psseq1i.mm"
include "psseq2i.mm"
include "bitri.mm"

theorem psseq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume psseq1i.1: |- A = B
  assume psseq12i.2: |- C = D


  assert |- ( A C. C <-> B C. D )

  proof
    cA
    cC
    wpss
    cB
    cC
    wpss
    cB
    cD
    wpss
    cA
    cB
    cC
    psseq1i.1
    psseq1i
    cC
    cD
    cB
    psseq12i.2
    psseq2i
    bitri
end
