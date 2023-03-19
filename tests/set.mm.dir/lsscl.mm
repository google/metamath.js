include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "islss.mm"
include "simp3bi.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem lsscl
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  assume lsscl.f: |- F = ( Scalar ` W )
  assume lsscl.b: |- B = ( Base ` F )
  assume lsscl.p: |- .+ = ( +g ` W )
  assume lsscl.t: |- .x. = ( .s ` W )
  assume lsscl.s: |- S = ( LSubSp ` W )


  assert |- ( ( U e. S /\ ( Z e. B /\ X e. U /\ Y e. U ) ) -> ( ( Z .x. X ) .+ Y ) e. U )

  proof
    cU
    cS
    wcel
    #
    vx
    cv
    #
    va
    cv
    #
    c.x
    co
    #
    vb
    cv
    #
    c.pl
    co
    #
    cU
    wcel
    #
    vb
    cU
    wral
    va
    cU
    wral
    vx
    cB
    wral
    #
    cZ
    cB
    wcel
    cX
    cU
    wcel
    cY
    cU
    wcel
    w3a
    cZ
    cX
    c.x
    co
    #
    cY
    c.pl
    co
    #
    cU
    wcel
    #
    @0
    cU
    cW
    cbs
    cfv
    #
    wss
    cU
    c0
    wne
    @7
    vx
    cB
    c.pl
    cS
    c.x
    cU
    cF
    @11
    cW
    va
    vb
    lsscl.f
    lsscl.b
    @11
    eqid
    lsscl.p
    lsscl.t
    lsscl.s
    islss
    simp3bi
    @6
    @10
    cZ
    @2
    c.x
    co
    #
    @4
    c.pl
    co
    #
    cU
    wcel
    @8
    @4
    c.pl
    co
    #
    cU
    wcel
    vx
    va
    vb
    cZ
    cX
    cY
    cB
    cU
    cU
    @1
    cZ
    wceq
    #
    @5
    @13
    cU
    @15
    @3
    @12
    @4
    c.pl
    @1
    cZ
    @2
    c.x
    oveq1
    oveq1d
    eleq1d
    @2
    cX
    wceq
    #
    @13
    @14
    cU
    @16
    @12
    @8
    @4
    c.pl
    @2
    cX
    cZ
    c.x
    oveq2
    oveq1d
    eleq1d
    @4
    cY
    wceq
    @14
    @9
    cU
    @4
    cY
    @8
    c.pl
    oveq2
    eleq1d
    rspc3v
    mpan9
end
