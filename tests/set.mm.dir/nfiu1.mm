include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "df-iun.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfiu1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- F/_ x U_ x e. A B

  proof
    vx
    vx
    cA
    cB
    ciun
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    vy
    cab
    vx
    vy
    cA
    cB
    df-iun
    @1
    vx
    vy
    @0
    vx
    cA
    nfre1
    nfab
    nfcxfr
end
