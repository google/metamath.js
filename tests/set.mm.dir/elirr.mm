include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "id.mm"
include "eleq12d.mm"
include "notbid.mm"
include "elirrv.mm"
include "vtoclg.mm"
include "pm2.01.mm"
include "ax-mp.mm"

theorem elirr
  let cA: class A
  let vx: setvar x


  assert |- -. A e. A

  proof
    cA
    cA
    wcel
    #
    @0
    wn
    #
    wi
    @1
    vx
    cv
    #
    @2
    wcel
    #
    wn
    @1
    vx
    cA
    cA
    @2
    cA
    wceq
    #
    @3
    @0
    @4
    @2
    cA
    @2
    cA
    @4
    id
    #
    @5
    eleq12d
    notbid
    vx
    elirrv
    vtoclg
    @0
    pm2.01
    ax-mp
end
