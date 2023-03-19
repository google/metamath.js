include "wnfc.mm"
include "wb.mm"
include "wtru.mm"
include "nftru.mm"
include "wceq.mm"
include "a1i.mm"
include "nfceqdf.mm"
include "trud.mm"

theorem nfceqi
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfceqi.1: |- A = B


  assert |- ( F/_ x A <-> F/_ x B )

  proof
    vx
    cA
    wnfc
    vx
    cB
    wnfc
    wb
    wtru
    vx
    cA
    cB
    vx
    nftru
    cA
    cB
    wceq
    wtru
    nfceqi.1
    a1i
    nfceqdf
    trud
end
