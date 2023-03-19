include "wcel.mm"
include "clss.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cvsca.mm"
include "cplusg.mm"
include "csca.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "2ralbidv.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "df-lss.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem lssset
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let cU: class U
  assume lssset.f: |- F = ( Scalar ` W )
  assume lssset.b: |- B = ( Base ` F )
  assume lssset.v: |- V = ( Base ` W )
  assume lssset.p: |- .+ = ( +g ` W )
  assume lssset.t: |- .x. = ( .s ` W )
  assume lssset.s: |- S = ( LSubSp ` W )

  disjoint .+ s
  disjoint s x
  disjoint B s
  disjoint B x
  disjoint V s
  disjoint a b
  disjoint a s
  disjoint a x
  disjoint W a
  disjoint b s
  disjoint b x
  disjoint W b
  disjoint W s
  disjoint W x
  disjoint .x. s
  disjoint s w
  disjoint .+ w
  disjoint w x
  disjoint B w
  disjoint V w
  disjoint a w
  disjoint b w
  disjoint W w
  disjoint .x. w
  disjoint U a
  disjoint U b
  disjoint U s
  disjoint U x
  assert |- ( W e. X -> S = { s e. ( ~P V \ { (/) } ) | A. x e. B A. a e. s A. b e. s ( ( x .x. a ) .+ b ) e. s } )

  proof
    cW
    cX
    wcel
    #
    cS
    cW
    clss
    cfv
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
    vs
    cv
    #
    wcel
    #
    vb
    @7
    wral
    va
    @7
    wral
    #
    vx
    cB
    wral
    #
    vs
    cV
    cpw
    #
    c0
    csn
    #
    cdif
    #
    crab
    #
    lssset.s
    @0
    cW
    cvv
    wcel
    @1
    @14
    wceq
    cW
    cX
    elex
    vw
    cW
    @2
    @3
    vw
    cv
    #
    cvsca
    cfv
    #
    co
    #
    @5
    @15
    cplusg
    cfv
    #
    co
    #
    @7
    wcel
    #
    vb
    @7
    wral
    va
    @7
    wral
    #
    vx
    @15
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    vs
    @15
    cbs
    cfv
    #
    cpw
    #
    @12
    cdif
    #
    crab
    @14
    cvv
    clss
    @15
    cW
    wceq
    #
    @24
    @10
    vs
    @27
    @13
    @28
    @26
    @11
    @12
    @28
    @25
    cV
    @28
    @25
    cW
    cbs
    cfv
    #
    cV
    @15
    cW
    cbs
    fveq2
    lssset.v
    syl6eqr
    pweqd
    difeq1d
    @28
    @21
    @9
    vx
    @23
    cB
    @28
    @23
    cF
    cbs
    cfv
    cB
    @28
    @22
    cF
    cbs
    @28
    @22
    cW
    csca
    cfv
    cF
    @15
    cW
    csca
    fveq2
    lssset.f
    syl6eqr
    fveq2d
    lssset.b
    syl6eqr
    @28
    @20
    @8
    va
    vb
    @7
    @7
    @28
    @19
    @6
    @7
    @28
    @19
    @4
    @5
    @18
    co
    @6
    @28
    @17
    @4
    @5
    @18
    @28
    @16
    c.x
    @2
    @3
    @28
    @16
    cW
    cvsca
    cfv
    c.x
    @15
    cW
    cvsca
    fveq2
    lssset.t
    syl6eqr
    oveqd
    oveq1d
    @28
    @18
    c.pl
    @4
    @5
    @28
    @18
    cW
    cplusg
    cfv
    c.pl
    @15
    cW
    cplusg
    fveq2
    lssset.p
    syl6eqr
    oveqd
    eqtrd
    eleq1d
    2ralbidv
    raleqbidv
    rabeqbidv
    vx
    vw
    vs
    va
    vb
    df-lss
    @10
    vs
    @13
    @11
    cvv
    wcel
    @13
    cvv
    wcel
    cV
    cV
    @29
    cvv
    lssset.v
    cW
    cbs
    fvex
    eqeltri
    pwex
    @11
    @12
    cvv
    difexg
    ax-mp
    rabex
    fvmpt
    syl
    syl5eq
end
