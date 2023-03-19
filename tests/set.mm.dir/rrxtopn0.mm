include "c0.mm"
include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "csn.mm"
include "ctopon.mm"
include "wcel.mm"
include "cpw.mm"
include "wceq.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cfn.mm"
include "0fin.mm"
include "eqid.mm"
include "rrxtoponfi.mm"
include "ax-mp.mm"
include "cvv.mm"
include "reex.mm"
include "mapdm0.mm"
include "fveq2i.mm"
include "eleqtri.mm"
include "topsn.mm"

theorem rrxtopn0
  let vk: setvar k
  let vx: setvar x


  assert |- ( TopOpen ` ( RR^ ` (/) ) ) = ~P { (/) }

  proof
    c0
    crrx
    cfv
    ctopn
    cfv
    #
    c0
    csn
    #
    ctopon
    cfv
    #
    wcel
    @0
    @1
    cpw
    wceq
    @0
    cr
    c0
    cmap
    co
    #
    ctopon
    cfv
    #
    @2
    c0
    cfn
    wcel
    @0
    @4
    wcel
    0fin
    c0
    @0
    @0
    eqid
    rrxtoponfi
    ax-mp
    @3
    @1
    ctopon
    cr
    cvv
    wcel
    @3
    @1
    wceq
    reex
    cr
    cvv
    mapdm0
    ax-mp
    fveq2i
    eleqtri
    c0
    @0
    topsn
    ax-mp
end
