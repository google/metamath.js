include "wel.mm"
include "wn.mm"
include "wral.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "eleq2.mm"
include "bitrd.mm"
include "notbid.mm"
include "rspccv.mm"
include "pm2.01d.mm"

theorem untelirr
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A. x e. A -. x e. x -> -. A e. A )

  proof
    vx
    vx
    wel
    #
    wn
    #
    vx
    cA
    wral
    cA
    cA
    wcel
    #
    @1
    @2
    wn
    vx
    cA
    cA
    vx
    cv
    #
    cA
    wceq
    #
    @0
    @2
    @4
    @0
    cA
    @3
    wcel
    @2
    @3
    cA
    @3
    eleq1
    @3
    cA
    cA
    eleq2
    bitrd
    notbid
    rspccv
    pm2.01d
end
