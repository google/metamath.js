include "cv.mm"
include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "csn.mm"
include "clvec.mm"
include "adantr.mm"
include "wpss.mm"
include "cdif.mm"
include "simpr.mm"
include "lsppratlem3.mm"
include "lsppratlem4.mm"
include "lsppratlem1.mm"
include "mpjaodan.mm"
include "simprl.mm"
include "simprr.mm"
include "lsppratlem2.mm"
include "mpdan.mm"

theorem lsppratlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cU: class U
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lspprat.v: |- V = ( Base ` W )
  assume lspprat.s: |- S = ( LSubSp ` W )
  assume lspprat.n: |- N = ( LSpan ` W )
  assume lspprat.w: |- ( ph -> W e. LVec )
  assume lspprat.u: |- ( ph -> U e. S )
  assume lspprat.x: |- ( ph -> X e. V )
  assume lspprat.y: |- ( ph -> Y e. V )
  assume lspprat.p: |- ( ph -> U C. ( N ` { X , Y } ) )
  assume lsppratlem1.o: |- .0. = ( 0g ` W )
  assume lsppratlem1.x2: |- ( ph -> x e. ( U \ { .0. } ) )
  assume lsppratlem1.y2: |- ( ph -> y e. ( U \ ( N ` { x } ) ) )


  assert |- ( ph -> ( N ` { X , Y } ) C_ U )

  proof
    wph
    cX
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cN
    cfv
    #
    wcel
    #
    cY
    @2
    wcel
    #
    wa
    #
    cX
    cY
    cpr
    cN
    cfv
    #
    cU
    wss
    wph
    @0
    cY
    csn
    cN
    cfv
    wcel
    #
    @5
    cX
    @0
    cY
    cpr
    cN
    cfv
    wcel
    #
    wph
    @7
    wa
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
    @7
    lspprat.w
    adantr
    wph
    cU
    cS
    wcel
    #
    @7
    lspprat.u
    adantr
    wph
    cX
    cV
    wcel
    #
    @7
    lspprat.x
    adantr
    wph
    cY
    cV
    wcel
    #
    @7
    lspprat.y
    adantr
    wph
    cU
    @6
    wpss
    #
    @7
    lspprat.p
    adantr
    lsppratlem1.o
    wph
    @0
    cU
    c.0
    csn
    cdif
    wcel
    #
    @7
    lsppratlem1.x2
    adantr
    wph
    @1
    cU
    @0
    csn
    cN
    cfv
    cdif
    wcel
    #
    @7
    lsppratlem1.y2
    adantr
    wph
    @7
    simpr
    lsppratlem3
    wph
    @8
    wa
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
    @9
    @8
    lspprat.w
    adantr
    wph
    @10
    @8
    lspprat.u
    adantr
    wph
    @11
    @8
    lspprat.x
    adantr
    wph
    @12
    @8
    lspprat.y
    adantr
    wph
    @13
    @8
    lspprat.p
    adantr
    lsppratlem1.o
    wph
    @14
    @8
    lsppratlem1.x2
    adantr
    wph
    @15
    @8
    lsppratlem1.y2
    adantr
    wph
    @8
    simpr
    lsppratlem4
    wph
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
    lspprat.w
    lspprat.u
    lspprat.x
    lspprat.y
    lspprat.p
    lsppratlem1.o
    lsppratlem1.x2
    lsppratlem1.y2
    lsppratlem1
    mpjaodan
    wph
    @5
    wa
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
    @9
    @5
    lspprat.w
    adantr
    wph
    @10
    @5
    lspprat.u
    adantr
    wph
    @11
    @5
    lspprat.x
    adantr
    wph
    @12
    @5
    lspprat.y
    adantr
    wph
    @13
    @5
    lspprat.p
    adantr
    lsppratlem1.o
    wph
    @14
    @5
    lsppratlem1.x2
    adantr
    wph
    @15
    @5
    lsppratlem1.y2
    adantr
    wph
    @3
    @4
    simprl
    wph
    @3
    @4
    simprr
    lsppratlem2
    mpdan
end
