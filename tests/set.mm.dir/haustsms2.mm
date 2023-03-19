include "ctsu.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wmo.mm"
include "wi.mm"
include "simpr.mm"
include "haustsms.mm"
include "adantr.mm"
include "eleq1.mm"
include "moi2.mm"
include "ancom2s.mm"
include "expr.mm"
include "syl21anc.mm"
include "velsn.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "wss.mm"
include "snssi.mm"
include "adantl.mm"
include "eqssd.mm"
include "ex.mm"

theorem haustsms2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tsmscl.b: |- B = ( Base ` G )
  assume tsmscl.1: |- ( ph -> G e. CMnd )
  assume tsmscl.2: |- ( ph -> G e. TopSp )
  assume tsmscl.a: |- ( ph -> A e. V )
  assume tsmscl.f: |- ( ph -> F : A --> B )
  assume haustsms.j: |- J = ( TopOpen ` G )
  assume haustsms.h: |- ( ph -> J e. Haus )


  assert |- ( ph -> ( X e. ( G tsums F ) -> ( G tsums F ) = { X } ) )

  proof
    wph
    cX
    cG
    cF
    ctsu
    co
    #
    wcel
    #
    @0
    cX
    csn
    #
    wceq
    wph
    @1
    wa
    #
    @0
    @2
    @3
    vx
    @0
    @2
    @3
    vx
    cv
    #
    @0
    wcel
    #
    @4
    cX
    wceq
    #
    @4
    @2
    wcel
    @3
    @1
    @5
    vx
    wmo
    #
    @1
    @5
    @6
    wi
    wph
    @1
    simpr
    #
    wph
    @7
    @1
    wph
    vx
    cA
    cB
    cF
    cG
    cJ
    cV
    tsmscl.b
    tsmscl.1
    tsmscl.2
    tsmscl.a
    tsmscl.f
    haustsms.j
    haustsms.h
    haustsms
    adantr
    @8
    @1
    @7
    wa
    #
    @1
    @5
    @6
    @9
    @5
    @1
    @6
    @5
    @1
    vx
    cX
    @0
    @4
    cX
    @0
    eleq1
    moi2
    ancom2s
    expr
    syl21anc
    vx
    cX
    velsn
    syl6ibr
    ssrdv
    @1
    @2
    @0
    wss
    wph
    cX
    @0
    snssi
    adantl
    eqssd
    ex
end
