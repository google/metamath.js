include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "co.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "lssvscl.mm"
include "syl22anc.mm"

theorem lcdlssvscl
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lcdlssvscl.h: |- H = ( LHyp ` K )
  assume lcdlssvscl.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdlssvscl.f: |- F = ( Scalar ` U )
  assume lcdlssvscl.r: |- R = ( Base ` F )
  assume lcdlssvscl.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlssvscl.v: |- V = ( Base ` C )
  assume lcdlssvscl.t: |- .x. = ( .s ` C )
  assume lcdlssvscl.s: |- S = ( LSubSp ` C )
  assume lcdlssvscl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdlssvscl.l: |- ( ph -> L e. S )
  assume lcdlssvscl.x: |- ( ph -> X e. R )
  assume lcdlssvscl.y: |- ( ph -> Y e. L )


  assert |- ( ph -> ( X .x. Y ) e. L )

  proof
    wph
    cC
    clmod
    wcel
    cL
    cS
    wcel
    cX
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    cY
    cL
    wcel
    cX
    cY
    c.x
    co
    cL
    wcel
    wph
    cC
    cH
    cK
    cW
    lcdlssvscl.h
    lcdlssvscl.c
    lcdlssvscl.k
    lcdlmod
    lcdlssvscl.l
    wph
    cX
    cR
    @1
    lcdlssvscl.x
    wph
    cC
    @1
    @0
    cU
    cF
    cH
    cK
    cR
    cW
    lcdlssvscl.h
    lcdlssvscl.u
    lcdlssvscl.f
    lcdlssvscl.r
    lcdlssvscl.c
    @0
    eqid
    #
    @1
    eqid
    #
    lcdlssvscl.k
    lcdsbase
    eleqtrrd
    lcdlssvscl.y
    @1
    cS
    c.x
    cL
    @0
    cC
    cX
    cY
    @2
    lcdlssvscl.t
    @3
    lcdlssvscl.s
    lssvscl
    syl22anc
end
