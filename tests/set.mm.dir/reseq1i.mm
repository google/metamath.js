include "wceq.mm"
include "cres.mm"
include "reseq1.mm"
include "ax-mp.mm"

theorem reseq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume reseqi.1: |- A = B


  assert |- ( A |` C ) = ( B |` C )

  proof
    cA
    cB
    wceq
    cA
    cC
    cres
    cB
    cC
    cres
    wceq
    reseqi.1
    cA
    cB
    cC
    reseq1
    ax-mp
end
