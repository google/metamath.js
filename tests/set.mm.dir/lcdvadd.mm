include "cplusg.mm"
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
include "ressplusg.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem lcdvadd
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  assume lcdvadd.h: |- H = ( LHyp ` K )
  assume lcdvadd.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvadd.d: |- D = ( LDual ` U )
  assume lcdvadd.a: |- .+ = ( +g ` D )
  assume lcdvadd.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvadd.p: |- .+b = ( +g ` C )
  assume lcdvadd.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> .+b = .+ )

  proof
    wph
    cC
    cplusg
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
    cplusg
    cfv
    #
    c.pb
    c.pl
    wph
    cC
    @6
    cplusg
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
    lcdvadd.h
    @2
    eqid
    lcdvadd.c
    lcdvadd.u
    @4
    eqid
    @0
    eqid
    lcdvadd.d
    lcdvadd.k
    lcdval
    fveq2d
    lcdvadd.p
    @5
    cvv
    wcel
    c.pl
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
    c.pl
    cD
    @6
    cvv
    @6
    eqid
    lcdvadd.a
    ressplusg
    ax-mp
    3eqtr4g
end
