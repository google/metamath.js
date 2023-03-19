include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "wo.mm"
include "ctcl.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "exmid.mm"
include "trclfvlb.mm"
include "fvprc.mm"
include "orim12i.mm"
include "ax-mp.mm"

theorem trclfvg
  let cR: class R


  assert |- ( R C_ ( t+ ` R ) \/ ( t+ ` R ) = (/) )

  proof
    cR
    cvv
    wcel
    #
    @0
    wn
    #
    wo
    cR
    cR
    ctcl
    cfv
    #
    wss
    #
    @2
    c0
    wceq
    #
    wo
    @0
    exmid
    @0
    @3
    @1
    @4
    cR
    cvv
    trclfvlb
    cR
    ctcl
    fvprc
    orim12i
    ax-mp
end
