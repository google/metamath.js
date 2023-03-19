include "wnfc.mm"
include "cv.mm"
include "wcel.mm"
include "wnf.mm"
include "df-nfc.mm"
include "mpgbir.mm"

theorem nfci
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nfci.1: |- F/ x y e. A

  disjoint x y
  disjoint A y
  assert |- F/_ x A

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
    vy
    vx
    vy
    cA
    df-nfc
    nfci.1
    mpgbir
end
