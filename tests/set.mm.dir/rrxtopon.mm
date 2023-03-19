include "wcel.mm"
include "crrx.mm"
include "cfv.mm"
include "ctps.mm"
include "cbs.mm"
include "ctopon.mm"
include "rrxtps.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"

theorem rrxtopon
  let cI: class I
  let cJ: class J
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume rrxtopon.1: |- J = ( TopOpen ` ( RR^ ` I ) )


  assert |- ( I e. V -> J e. ( TopOn ` ( Base ` ( RR^ ` I ) ) ) )

  proof
    cI
    cV
    wcel
    cI
    crrx
    cfv
    #
    ctps
    wcel
    cJ
    @0
    cbs
    cfv
    #
    ctopon
    cfv
    wcel
    cI
    cV
    rrxtps
    @1
    cJ
    @0
    @1
    eqid
    rrxtopon.1
    istps
    sylib
end
