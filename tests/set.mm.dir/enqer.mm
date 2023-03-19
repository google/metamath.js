include "cmi.mm"
include "ceq.mm"
include "cnpi.mm"
include "df-enq.mm"
include "cv.mm"
include "mulcompi.mm"
include "mulclpi.mm"
include "mulasspi.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "mulcanpi.mm"
include "biimpd.mm"
include "ecopover.mm"

theorem enqer
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ~Q Er ( N. X. N. )

  proof
    vx
    vy
    vz
    vw
    vv
    vu
    cmi
    ceq
    cnpi
    vx
    vy
    vz
    vw
    vv
    vu
    df-enq
    vx
    cv
    #
    vy
    cv
    #
    mulcompi
    @0
    @1
    mulclpi
    @0
    @1
    vz
    cv
    #
    mulasspi
    @0
    cnpi
    wcel
    @1
    cnpi
    wcel
    wa
    @0
    @1
    cmi
    co
    @0
    @2
    cmi
    co
    wceq
    @1
    @2
    wceq
    @0
    @1
    @2
    mulcanpi
    biimpd
    ecopover
end
