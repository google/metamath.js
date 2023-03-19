include "cima.mm"
include "cdif.mm"
include "cun.mm"
include "wss.mm"
include "ssun2.mm"
include "undif2.mm"
include "sseqtr4i.mm"
include "imass2.mm"
include "ax-mp.mm"
include "imaundi.mm"
include "sseqtri.mm"
include "ssundif.mm"
include "mpbi.mm"

theorem imadifss
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F " A ) \ ( F " B ) ) C_ ( F " ( A \ B ) )

  proof
    cF
    cA
    cima
    #
    cF
    cB
    cima
    #
    cF
    cA
    cB
    cdif
    #
    cima
    #
    cun
    #
    wss
    @0
    @1
    cdif
    @3
    wss
    @0
    cF
    cB
    @2
    cun
    #
    cima
    #
    @4
    cA
    @5
    wss
    @0
    @6
    wss
    cA
    cB
    cA
    cun
    @5
    cA
    cB
    ssun2
    cB
    cA
    undif2
    sseqtr4i
    cA
    @5
    cF
    imass2
    ax-mp
    cF
    cB
    @2
    imaundi
    sseqtri
    @0
    @1
    @3
    ssundif
    mpbi
end
