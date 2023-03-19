include "cc0.mm"
include "cblen.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "cabs.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "caddc.mm"
include "cif.mm"
include "cvv.mm"
include "wcel.mm"
include "c0ex.mm"
include "blenval.mm"
include "ax-mp.mm"
include "eqid.mm"
include "iftruei.mm"
include "eqtri.mm"

theorem blen0
  let vk: setvar k
  let vx: setvar x


  assert |- ( #b ` 0 ) = 1

  proof
    cc0
    cblen
    cfv
    #
    cc0
    cc0
    wceq
    #
    c1
    c2
    cc0
    cabs
    cfv
    clogb
    co
    cfl
    cfv
    c1
    caddc
    co
    #
    cif
    #
    c1
    cc0
    cvv
    wcel
    @0
    @3
    wceq
    c0ex
    cc0
    cvv
    blenval
    ax-mp
    @1
    c1
    @2
    cc0
    eqid
    iftruei
    eqtri
end
