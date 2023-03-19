include "wcel.mm"
include "wfo.mm"
include "wss.mm"
include "cqtop.mm"
include "co.mm"
include "ccnv.mm"
include "cima.mm"
include "wa.mm"
include "wb.mm"
include "ssid.mm"
include "elqtop.mm"
include "mp3an3.mm"

theorem elqtop2
  let cA: class A
  let cF: class F
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume qtoptop.1: |- X = U. J


  assert |- ( ( J e. V /\ F : X -onto-> Y ) -> ( A e. ( J qTop F ) <-> ( A C_ Y /\ ( `' F " A ) e. J ) ) )

  proof
    cJ
    cV
    wcel
    cX
    cY
    cF
    wfo
    cX
    cX
    wss
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
    cX
    ssid
    cA
    cF
    cJ
    cV
    cX
    cY
    cX
    qtoptop.1
    elqtop
    mp3an3
end
