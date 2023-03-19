include "wne.mm"
include "ciedg.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "ssid.mm"
include "wb.mm"
include "sseq2.mm"
include "adantl.mm"
include "mpbiri.mm"
include "mpidan.mm"

theorem upgr1wlkdlem2
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume upgr1wlkd.p: |- P = <" X Y ">
  assume upgr1wlkd.f: |- F = <" J ">
  assume upgr1wlkd.x: |- ( ph -> X e. ( Vtx ` G ) )
  assume upgr1wlkd.y: |- ( ph -> Y e. ( Vtx ` G ) )
  assume upgr1wlkd.j: |- ( ph -> ( ( iEdg ` G ) ` J ) = { X , Y } )


  assert |- ( ( ph /\ X =/= Y ) -> { X , Y } C_ ( ( iEdg ` G ) ` J ) )

  proof
    wph
    cX
    cY
    wne
    #
    cJ
    cG
    ciedg
    cfv
    cfv
    #
    cX
    cY
    cpr
    #
    wceq
    #
    @2
    @1
    wss
    #
    upgr1wlkd.j
    wph
    @0
    wa
    #
    @3
    wa
    @4
    @2
    @2
    wss
    #
    @2
    ssid
    @3
    @4
    @6
    wb
    @5
    @1
    @2
    @2
    sseq2
    adantl
    mpbiri
    mpidan
end
