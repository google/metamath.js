include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "df-iun.mm"
include "nfcri.mm"
include "nfrex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfiun
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfiun.1: |- F/_ y A
  assume nfiun.2: |- F/_ y B


  assert |- F/_ y U_ x e. A B

  proof
    vy
    vx
    cA
    cB
    ciun
    vz
    cv
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    vz
    cab
    vx
    vz
    cA
    cB
    df-iun
    @1
    vy
    vz
    @0
    vy
    vx
    cA
    nfiun.1
    vy
    vz
    cB
    nfiun.2
    nfcri
    nfrex
    nfab
    nfcxfr
end
