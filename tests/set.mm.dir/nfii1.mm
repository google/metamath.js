include "ciin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cab.mm"
include "df-iin.mm"
include "nfra1.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfii1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- F/_ x |^|_ x e. A B

  proof
    vx
    vx
    cA
    cB
    ciin
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wral
    #
    vy
    cab
    vx
    vy
    cA
    cB
    df-iin
    @1
    vx
    vy
    @0
    vx
    cA
    nfra1
    nfab
    nfcxfr
end
