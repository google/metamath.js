include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cperf.mm"
include "cuni.mm"
include "clp.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "ctopon.mm"
include "crest.mm"
include "co.mm"
include "toptopon.mm"
include "resttopon.mm"
include "sylanb.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "syl.mm"
include "eqid.mm"
include "isperf.mm"
include "baib.mm"
include "cin.mm"
include "sseqin2.mm"
include "ssid.mm"
include "restlp.mm"
include "mp3an3.mm"
include "toponuni.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "eqeq12d.mm"
include "syl5bb.mm"
include "bitr4d.mm"

theorem restperf
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vo: setvar o
  let vx: setvar x
  let cS: class S
  assume restcls.1: |- X = U. J
  assume restcls.2: |- K = ( J |`t Y )


  assert |- ( ( J e. Top /\ Y C_ X ) -> ( K e. Perf <-> Y C_ ( ( limPt ` J ) ` Y ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cY
    cX
    wss
    #
    wa
    #
    cK
    cperf
    wcel
    #
    cK
    cuni
    #
    cK
    clp
    cfv
    #
    cfv
    #
    @4
    wceq
    #
    cY
    cY
    cJ
    clp
    cfv
    cfv
    #
    wss
    #
    @2
    cK
    ctop
    wcel
    #
    @3
    @7
    wb
    @2
    cK
    cY
    ctopon
    cfv
    #
    wcel
    #
    @10
    @2
    cK
    cJ
    cY
    crest
    co
    #
    @11
    restcls.2
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    @1
    @13
    @11
    wcel
    cJ
    cX
    restcls.1
    toptopon
    cY
    cJ
    cX
    resttopon
    sylanb
    syl5eqel
    #
    cY
    cK
    topontop
    syl
    @3
    @10
    @7
    cK
    @4
    @4
    eqid
    isperf
    baib
    syl
    @9
    @8
    cY
    cin
    #
    cY
    wceq
    @2
    @7
    cY
    @8
    sseqin2
    @2
    @15
    @6
    cY
    @4
    @2
    cY
    @5
    cfv
    #
    @15
    @6
    @0
    @1
    cY
    cY
    wss
    @16
    @15
    wceq
    cY
    ssid
    cY
    cJ
    cK
    cX
    cY
    restcls.1
    restcls.2
    restlp
    mp3an3
    @2
    cY
    @4
    @5
    @2
    @12
    cY
    @4
    wceq
    @14
    cY
    cK
    toponuni
    syl
    #
    fveq2d
    eqtr3d
    @17
    eqeq12d
    syl5bb
    bitr4d
end
