include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "wceq.mm"
include "wb.mm"
include "nfab1.mm"
include "cleqf.mm"
include "abid.mm"
include "mpgbir.mm"

theorem abid2f
  let vx: setvar x
  let cA: class A
  assume abid2f.1: |- F/_ x A


  assert |- { x | x e. A } = A

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vx
    cab
    #
    cA
    wceq
    @0
    @2
    wcel
    @1
    wb
    vx
    vx
    @2
    cA
    @1
    vx
    nfab1
    abid2f.1
    cleqf
    @1
    vx
    abid
    mpgbir
end
