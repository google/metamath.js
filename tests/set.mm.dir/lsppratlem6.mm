include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "wss.mm"
include "cpr.mm"
include "wpss.mm"
include "adantr.mm"
include "wn.mm"
include "clvec.mm"
include "simprl.mm"
include "simprr.mm"
include "lsppratlem5.mm"
include "ssnpss.mm"
include "syl.mm"
include "expr.mm"
include "mt2d.mm"
include "eq0rdv.mm"
include "ssdif0.mm"
include "sylibr.mm"
include "clmod.mm"
include "lveclmod.mm"
include "eldifi.mm"
include "adantl.mm"
include "lspsnel5a.mm"
include "eqssd.mm"
include "ex.mm"

theorem lsppratlem6
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vy: setvar y
  assume lspprat.v: |- V = ( Base ` W )
  assume lspprat.s: |- S = ( LSubSp ` W )
  assume lspprat.n: |- N = ( LSpan ` W )
  assume lspprat.w: |- ( ph -> W e. LVec )
  assume lspprat.u: |- ( ph -> U e. S )
  assume lspprat.x: |- ( ph -> X e. V )
  assume lspprat.y: |- ( ph -> Y e. V )
  assume lspprat.p: |- ( ph -> U C. ( N ` { X , Y } ) )
  assume lsppratlem6.o: |- .0. = ( 0g ` W )


  assert |- ( ph -> ( x e. ( U \ { .0. } ) -> U = ( N ` { x } ) ) )

  proof
    wph
    vx
    cv
    #
    cU
    c.0
    csn
    #
    cdif
    wcel
    #
    cU
    @0
    csn
    cN
    cfv
    #
    wceq
    wph
    @2
    wa
    #
    cU
    @3
    @4
    cU
    @3
    cdif
    #
    c0
    wceq
    cU
    @3
    wss
    @4
    vy
    @5
    @4
    vy
    cv
    @5
    wcel
    #
    cU
    cX
    cY
    cpr
    cN
    cfv
    #
    wpss
    #
    wph
    @8
    @2
    lspprat.p
    adantr
    wph
    @2
    @6
    @8
    wn
    #
    wph
    @2
    @6
    wa
    #
    wa
    #
    @7
    cU
    wss
    @9
    @11
    vx
    vy
    cS
    cU
    cN
    cV
    cW
    cX
    cY
    c.0
    lspprat.v
    lspprat.s
    lspprat.n
    wph
    cW
    clvec
    wcel
    #
    @10
    lspprat.w
    adantr
    wph
    cU
    cS
    wcel
    #
    @10
    lspprat.u
    adantr
    wph
    cX
    cV
    wcel
    @10
    lspprat.x
    adantr
    wph
    cY
    cV
    wcel
    @10
    lspprat.y
    adantr
    wph
    @8
    @10
    lspprat.p
    adantr
    lsppratlem6.o
    wph
    @2
    @6
    simprl
    wph
    @2
    @6
    simprr
    lsppratlem5
    @7
    cU
    ssnpss
    syl
    expr
    mt2d
    eq0rdv
    cU
    @3
    ssdif0
    sylibr
    @4
    cS
    cU
    cN
    cW
    @0
    lspprat.s
    lspprat.n
    wph
    cW
    clmod
    wcel
    #
    @2
    wph
    @12
    @14
    lspprat.w
    cW
    lveclmod
    syl
    adantr
    wph
    @13
    @2
    lspprat.u
    adantr
    @2
    @0
    cU
    wcel
    wph
    @0
    cU
    @1
    eldifi
    adantl
    lspsnel5a
    eqssd
    ex
end
