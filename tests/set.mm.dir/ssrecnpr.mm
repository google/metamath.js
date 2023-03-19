include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "elpri.mm"
include "eqimss2.mm"
include "ax-resscn.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "jaoi.mm"
include "syl.mm"

theorem ssrecnpr
  let cS: class S


  assert |- ( S e. { RR , CC } -> RR C_ S )

  proof
    cS
    cr
    cc
    cpr
    wcel
    cS
    cr
    wceq
    #
    cS
    cc
    wceq
    #
    wo
    cr
    cS
    wss
    #
    cS
    cr
    cc
    elpri
    @0
    @2
    @1
    cr
    cS
    eqimss2
    @1
    @2
    cr
    cc
    wss
    ax-resscn
    cS
    cc
    cr
    sseq2
    mpbiri
    jaoi
    syl
end
