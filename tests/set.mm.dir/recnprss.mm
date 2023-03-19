include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "elpri.mm"
include "ax-resscn.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "eqimss.mm"
include "jaoi.mm"
include "syl.mm"

theorem recnprss
  let cS: class S


  assert |- ( S e. { RR , CC } -> S C_ CC )

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
    cS
    cc
    wss
    #
    cS
    cr
    cc
    elpri
    @0
    @2
    @1
    @0
    @2
    cr
    cc
    wss
    ax-resscn
    cS
    cr
    cc
    sseq1
    mpbiri
    cS
    cc
    eqimss
    jaoi
    syl
end
