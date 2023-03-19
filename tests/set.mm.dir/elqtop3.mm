include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wfo.mm"
include "cuni.mm"
include "wss.mm"
include "cqtop.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "toponuni.mm"
include "eqimss.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "elqtop.mm"
include "mpd3an3.mm"

theorem elqtop3
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ F : X -onto-> Y ) -> ( A e. ( J qTop F ) <-> ( A C_ Y /\ ( `' F " A ) e. J ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    cX
    cY
    cF
    wfo
    #
    cX
    cJ
    cuni
    #
    wss
    #
    cA
    cJ
    cF
    cqtop
    co
    wcel
    cA
    cY
    wss
    cF
    ccnv
    cA
    cima
    cJ
    wcel
    wa
    wb
    @1
    @4
    @2
    @1
    cX
    @3
    wceq
    @4
    cX
    cJ
    toponuni
    cX
    @3
    eqimss
    syl
    adantr
    cA
    cF
    cJ
    @0
    @3
    cY
    cX
    @3
    eqid
    elqtop
    mpd3an3
end
