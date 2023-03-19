include "cvsca.mm"
include "cfv.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "chlt.mm"
include "eqid.mm"
include "lcdval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "rabex.mm"
include "ressvsca.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem lcdvs
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  assume lcdvs.h: |- H = ( LHyp ` K )
  assume lcdvs.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvs.d: |- D = ( LDual ` U )
  assume lcdvs.t: |- .x. = ( .s ` D )
  assume lcdvs.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvs.m: |- .xb = ( .s ` C )
  assume lcdvs.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> .xb = .x. )

  proof
    wph
    cC
    cvsca
    cfv
    cD
    vf
    cv
    cU
    clk
    cfv
    #
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    @2
    cfv
    @1
    wceq
    #
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cress
    co
    #
    cvsca
    cfv
    #
    c.xb
    c.x
    wph
    cC
    @6
    cvsca
    wph
    cC
    cD
    cU
    vf
    @4
    cH
    cK
    @0
    @2
    cW
    chlt
    lcdvs.h
    @2
    eqid
    lcdvs.c
    lcdvs.u
    @4
    eqid
    @0
    eqid
    lcdvs.d
    lcdvs.k
    lcdval
    fveq2d
    lcdvs.m
    @5
    cvv
    wcel
    c.x
    @7
    wceq
    @3
    vf
    @4
    cU
    clfn
    fvex
    rabex
    @5
    c.x
    cD
    @6
    cvv
    @6
    eqid
    lcdvs.t
    ressvsca
    ax-mp
    3eqtr4g
end
