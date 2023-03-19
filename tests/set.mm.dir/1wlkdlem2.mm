include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "csn.mm"
include "snidg.mm"
include "syl.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "wne.mm"
include "cpr.mm"
include "wss.mm"
include "wb.mm"
include "prssg.mm"
include "syl2an2r.mm"
include "mpbird.mm"
include "simpld.mm"
include "pm2.61dane.mm"

theorem 1wlkdlem2
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">
  assume 1wlkd.x: |- ( ph -> X e. V )
  assume 1wlkd.y: |- ( ph -> Y e. V )
  assume 1wlkd.l: |- ( ( ph /\ X = Y ) -> ( I ` J ) = { X } )
  assume 1wlkd.j: |- ( ( ph /\ X =/= Y ) -> { X , Y } C_ ( I ` J ) )


  assert |- ( ph -> X e. ( I ` J ) )

  proof
    wph
    cX
    cJ
    cI
    cfv
    #
    wcel
    #
    cX
    cY
    wph
    cX
    cY
    wceq
    #
    wa
    cX
    cX
    csn
    #
    @0
    wph
    cX
    @3
    wcel
    #
    @2
    wph
    cX
    cV
    wcel
    #
    @4
    1wlkd.x
    cX
    cV
    snidg
    syl
    adantr
    1wlkd.l
    eleqtrrd
    wph
    cX
    cY
    wne
    #
    wa
    #
    @1
    cY
    @0
    wcel
    #
    @7
    @1
    @8
    wa
    #
    cX
    cY
    cpr
    @0
    wss
    #
    1wlkd.j
    wph
    @5
    @6
    cY
    cV
    wcel
    #
    @9
    @10
    wb
    1wlkd.x
    wph
    @11
    @6
    1wlkd.y
    adantr
    cX
    cY
    @0
    cV
    cV
    prssg
    syl2an2r
    mpbird
    simpld
    pm2.61dane
end
