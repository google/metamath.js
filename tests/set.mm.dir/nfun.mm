include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "cab.mm"
include "df-un.mm"
include "nfcri.mm"
include "nfor.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume nfun.1: |- F/_ x A
  assume nfun.2: |- F/_ x B


  assert |- F/_ x ( A u. B )

  proof
    vx
    cA
    cB
    cun
    vy
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wo
    #
    vy
    cab
    vy
    cA
    cB
    df-un
    @3
    vx
    vy
    @1
    @2
    vx
    vx
    vy
    cA
    nfun.1
    nfcri
    vx
    vy
    cB
    nfun.2
    nfcri
    nfor
    nfab
    nfcxfr
end
