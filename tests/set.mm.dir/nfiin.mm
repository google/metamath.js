include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "df-iin.mm"
include "nfcri.mm"
include "nfral.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfiin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume nfiun.1: |- F/_ y A
  assume nfiun.2: |- F/_ y B


  assert |- F/_ y |^|_ x e. A B

  proof
    vy
    vx
    cA
    cB
    ciin
    vz
    cv
    cB
    wcel
    #
    vx
    cA
    wral
    #
    vz
    cab
    vx
    vz
    cA
    cB
    df-iin
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
    nfral
    nfab
    nfcxfr
end
