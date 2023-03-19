include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "cpr.mm"
include "wn.mm"
include "wa.mm"
include "cun.mm"
include "clvec.mm"
include "wss.mm"
include "cdif.mm"
include "adantr.mm"
include "snssd.mm"
include "pssssd.mm"
include "eldifad.mm"
include "sseldd.mm"
include "prcom.mm"
include "df-pr.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "syl6eleq.mm"
include "anim1i.mm"
include "eldif.mm"
include "sylibr.mm"
include "lspsolv.mm"
include "syl13anc.mm"
include "eqtr3i.mm"
include "ex.mm"
include "orrd.mm"

theorem lsppratlem1
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


  assert |- ( ph -> ( x e. ( N ` { Y } ) \/ X e. ( N ` { x , Y } ) ) )

  proof
    wph
    vx
    cv
    #
    cY
    csn
    #
    cN
    cfv
    #
    wcel
    #
    cX
    @0
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wph
    @3
    wn
    #
    @6
    wph
    @7
    wa
    #
    cX
    @1
    @0
    csn
    cun
    #
    cN
    cfv
    #
    @5
    @8
    cW
    clvec
    wcel
    #
    @1
    cV
    wss
    #
    cX
    cV
    wcel
    #
    @0
    @1
    cX
    csn
    cun
    #
    cN
    cfv
    #
    @2
    cdif
    wcel
    #
    cX
    @10
    wcel
    wph
    @11
    @7
    lspprat.w
    adantr
    wph
    @12
    @7
    wph
    cY
    cV
    lspprat.y
    snssd
    adantr
    wph
    @13
    @7
    lspprat.x
    adantr
    @8
    @0
    @15
    wcel
    #
    @7
    wa
    @16
    wph
    @17
    @7
    wph
    @0
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    @15
    wph
    cU
    @19
    @0
    wph
    cU
    @19
    lspprat.p
    pssssd
    wph
    @0
    cU
    c.0
    csn
    lsppratlem1.x2
    eldifad
    sseldd
    @18
    @14
    cN
    @18
    cY
    cX
    cpr
    @14
    cX
    cY
    prcom
    cY
    cX
    df-pr
    eqtri
    fveq2i
    syl6eleq
    anim1i
    @0
    @15
    @2
    eldif
    sylibr
    @1
    cS
    cN
    cV
    cW
    @0
    cX
    lspprat.v
    lspprat.s
    lspprat.n
    lspsolv
    syl13anc
    @9
    @4
    cN
    cY
    @0
    cpr
    @9
    @4
    cY
    @0
    df-pr
    cY
    @0
    prcom
    eqtr3i
    fveq2i
    syl6eleq
    ex
    orrd
end
