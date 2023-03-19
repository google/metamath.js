include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wrmo.mm"
include "wal.mm"
include "df-disj.mm"
include "nfrmo1.mm"
include "nfal.mm"
include "nfxfr.mm"

theorem nfdisj1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- F/ x Disj_ x e. A B

  proof
    vx
    cA
    cB
    wdisj
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    vx
    vx
    vy
    cA
    cB
    df-disj
    @1
    vx
    vy
    @0
    vx
    cA
    nfrmo1
    nfal
    nfxfr
end
