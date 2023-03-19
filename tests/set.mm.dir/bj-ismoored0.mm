include "cmoore.mm"
include "wcel.mm"
include "cuni.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "cpw.mm"
include "wral.mm"
include "bj-ismoore.mm"
include "c0.mm"
include "wi.mm"
include "0elpw.mm"
include "wceq.mm"
include "rint0.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "pm2.43i.mm"

theorem bj-ismoored0
  let cA: class A
  let vx: setvar x


  assert |- ( A e. Moore_ -> U. A e. A )

  proof
    cA
    cmoore
    wcel
    #
    cA
    cuni
    #
    cA
    wcel
    #
    @0
    @0
    @1
    vx
    cv
    #
    cint
    cin
    #
    cA
    wcel
    #
    vx
    cA
    cpw
    #
    wral
    #
    @2
    vx
    cA
    cmoore
    bj-ismoore
    c0
    @6
    wcel
    @7
    @2
    wi
    cA
    0elpw
    @5
    @2
    vx
    c0
    @6
    @3
    c0
    wceq
    @4
    @1
    cA
    @1
    @3
    rint0
    eleq1d
    rspcv
    ax-mp
    syl6bi
    pm2.43i
end
