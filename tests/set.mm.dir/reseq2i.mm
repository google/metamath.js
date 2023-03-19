include "wceq.mm"
include "cres.mm"
include "reseq2.mm"
include "ax-mp.mm"

theorem reseq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume reseqi.1: |- A = B


  assert |- ( C |` A ) = ( C |` B )

  proof
    cA
    cB
    wceq
    cC
    cA
    cres
    cC
    cB
    cres
    wceq
    reseqi.1
    cA
    cB
    cC
    reseq2
    ax-mp
end
