include "cfn.mm"
include "wcel.mm"
include "crrx.mm"
include "cfv.mm"
include "cbs.mm"
include "ctopon.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "rrxtopon.mm"
include "id.mm"
include "eqid.mm"
include "rrxbasefi.mm"
include "fveq2d.mm"
include "eleqtrd.mm"

theorem rrxtoponfi
  let cI: class I
  let cJ: class J
  let vk: setvar k
  let vx: setvar x
  assume rrxtopfi.1: |- J = ( TopOpen ` ( RR^ ` I ) )


  assert |- ( I e. Fin -> J e. ( TopOn ` ( RR ^m I ) ) )

  proof
    cI
    cfn
    wcel
    #
    cJ
    cI
    crrx
    cfv
    #
    cbs
    cfv
    #
    ctopon
    cfv
    cr
    cI
    cmap
    co
    #
    ctopon
    cfv
    cI
    cJ
    cfn
    rrxtopfi.1
    rrxtopon
    @0
    @2
    @3
    ctopon
    @0
    @2
    @1
    cI
    @0
    id
    @1
    eqid
    @2
    eqid
    rrxbasefi
    fveq2d
    eleqtrd
end
