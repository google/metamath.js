include "wceq.mm"
include "wtru.mm"
include "nftru.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "a1i.mm"
include "eqrd.mm"
include "trud.mm"

theorem eqri
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume eqri.1: |- F/_ x A
  assume eqri.2: |- F/_ x B
  assume eqri.3: |- ( x e. A <-> x e. B )


  assert |- A = B

  proof
    cA
    cB
    wceq
    wtru
    vx
    cA
    cB
    vx
    nftru
    eqri.1
    eqri.2
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wb
    wtru
    eqri.3
    a1i
    eqrd
    trud
end
