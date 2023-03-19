include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "wo.mm"
include "cab.mm"
include "dfpr2.mm"
include "nfeq2.mm"
include "nfor.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfpr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume nfpr.1: |- F/_ x A
  assume nfpr.2: |- F/_ x B


  assert |- F/_ x { A , B }

  proof
    vx
    cA
    cB
    cpr
    vy
    cv
    #
    cA
    wceq
    #
    @0
    cB
    wceq
    #
    wo
    #
    vy
    cab
    vy
    cA
    cB
    dfpr2
    @3
    vx
    vy
    @1
    @2
    vx
    vx
    @0
    cA
    nfpr.1
    nfeq2
    vx
    @0
    cB
    nfpr.2
    nfeq2
    nfor
    nfab
    nfcxfr
end
