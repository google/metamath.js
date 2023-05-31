include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "wal.mm"
include "df-nfc.mm"
include "sp.mm"
include "sylbi.mm"

theorem nfcr
  param vx: setvar x
  param vy: setvar y
  param cA: class A

  disjoint x y
  disjoint A y
  assert |- ( F/_ x A -> F/ x y e. A )

  proof
    vx
    cA
    wnfc
    vy
    cv
    cA
    wcel
    vx
    wnf
    #
    vy
    wal
    @0
    vx
    vy
    cA
    df-nfc
    @0
    vy
    sp
    sylbi
end
