include "wceq.mm"
include "ciedg.mm"
include "cfv.mm"
include "csn.mm"
include "cpr.mm"
include "wi.mm"
include "wb.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "eqcoms.mm"
include "wa.mm"
include "simpl.mm"
include "dfsn2.mm"
include "syl6eqr.mm"
include "ex.mm"
include "syl6bi.mm"
include "com13.mm"
include "mpd.mm"
include "imp.mm"

theorem upgr1wlkdlem1
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


  assert |- ( ( ph /\ X = Y ) -> ( ( iEdg ` G ) ` J ) = { X } )

  proof
    wph
    cX
    cY
    wceq
    #
    cJ
    cG
    ciedg
    cfv
    cfv
    #
    cX
    csn
    #
    wceq
    #
    wph
    @1
    cX
    cY
    cpr
    #
    wceq
    #
    @0
    @3
    wi
    upgr1wlkd.j
    @0
    @5
    wph
    @3
    @0
    @5
    @1
    cX
    cX
    cpr
    #
    wceq
    #
    wph
    @3
    wi
    @5
    @7
    wb
    cY
    cX
    cY
    cX
    wceq
    @4
    @6
    @1
    cY
    cX
    cX
    preq2
    eqeq2d
    eqcoms
    @7
    wph
    @3
    @7
    wph
    wa
    @1
    @6
    @2
    @7
    wph
    simpl
    cX
    dfsn2
    syl6eqr
    ex
    syl6bi
    com13
    mpd
    imp
end
