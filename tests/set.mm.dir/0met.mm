include "c0.mm"
include "0ex.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "f0.mm"
include "xp0.mm"
include "feq2i.mm"
include "mpbir.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "noel.mm"
include "pm2.21i.mm"
include "adantr.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "3ad2ant1.mm"
include "ismeti.mm"

theorem 0met
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- (/) e. ( Met ` (/) )

  proof
    vx
    vy
    vz
    c0
    c0
    0ex
    c0
    c0
    cxp
    #
    cr
    c0
    wf
    c0
    cr
    c0
    wf
    cr
    f0
    @0
    c0
    cr
    c0
    c0
    xp0
    feq2i
    mpbir
    vx
    cv
    #
    c0
    wcel
    #
    @1
    vy
    cv
    #
    c0
    co
    #
    cc0
    wceq
    @1
    @3
    wceq
    wb
    #
    @3
    c0
    wcel
    #
    @2
    @5
    @1
    noel
    #
    pm2.21i
    adantr
    @2
    @6
    @4
    vz
    cv
    #
    @1
    c0
    co
    @8
    @3
    c0
    co
    caddc
    co
    cle
    wbr
    #
    @8
    c0
    wcel
    @2
    @9
    @7
    pm2.21i
    3ad2ant1
    ismeti
end
