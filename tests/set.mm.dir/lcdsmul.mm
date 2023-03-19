include "co.mm"
include "coppr.mm"
include "cfv.mm"
include "cmulr.mm"
include "eqid.mm"
include "lcdsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "opprmul.mm"
include "syl6eq.mm"

theorem lcdsmul
  let wph: wff ph
  let cC: class C
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lcdsmul.h: |- H = ( LHyp ` K )
  assume lcdsmul.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdsmul.f: |- F = ( Scalar ` U )
  assume lcdsmul.l: |- L = ( Base ` F )
  assume lcdsmul.t: |- .x. = ( .r ` F )
  assume lcdsmul.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdsmul.s: |- S = ( Scalar ` C )
  assume lcdsmul.m: |- .xb = ( .r ` S )
  assume lcdsmul.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdsmul.x: |- ( ph -> X e. L )
  assume lcdsmul.y: |- ( ph -> Y e. L )


  assert |- ( ph -> ( X .xb Y ) = ( Y .x. X ) )

  proof
    wph
    cX
    cY
    c.xb
    co
    cX
    cY
    cF
    coppr
    cfv
    #
    cmulr
    cfv
    #
    co
    cY
    cX
    c.x
    co
    wph
    c.xb
    @1
    cX
    cY
    wph
    c.xb
    cS
    cmulr
    cfv
    @1
    lcdsmul.m
    wph
    cS
    @0
    cmulr
    wph
    cC
    cS
    cU
    cF
    cH
    cK
    @0
    cW
    lcdsmul.h
    lcdsmul.u
    lcdsmul.f
    @0
    eqid
    #
    lcdsmul.c
    lcdsmul.s
    lcdsmul.k
    lcdsca
    fveq2d
    syl5eq
    oveqd
    cL
    cF
    @1
    c.x
    @0
    cX
    cY
    lcdsmul.l
    lcdsmul.t
    @2
    @1
    eqid
    opprmul
    syl6eq
end
