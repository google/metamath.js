include "csca.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "eqid.mm"
include "lcdsmul.mm"
include "oveq1d.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "lcdlmod.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "eqtr3d.mm"

theorem lcdvsass
  let wph: wff ph
  let cC: class C
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lcdvsass.h: |- H = ( LHyp ` K )
  assume lcdvsass.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvsass.r: |- R = ( Scalar ` U )
  assume lcdvsass.l: |- L = ( Base ` R )
  assume lcdvsass.t: |- .x. = ( .r ` R )
  assume lcdvsass.d: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvsass.f: |- F = ( Base ` C )
  assume lcdvsass.s: |- .xb = ( .s ` C )
  assume lcdvsass.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvsass.x: |- ( ph -> X e. L )
  assume lcdvsass.y: |- ( ph -> Y e. L )
  assume lcdvsass.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( Y .x. X ) .xb G ) = ( X .xb ( Y .xb G ) ) )

  proof
    wph
    cX
    cY
    cC
    csca
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    cG
    c.xb
    co
    #
    cY
    cX
    c.x
    co
    #
    cG
    c.xb
    co
    cX
    cY
    cG
    c.xb
    co
    c.xb
    co
    #
    wph
    @2
    @4
    cG
    c.xb
    wph
    cC
    @0
    @1
    c.x
    cU
    cR
    cH
    cK
    cL
    cW
    cX
    cY
    lcdvsass.h
    lcdvsass.u
    lcdvsass.r
    lcdvsass.l
    lcdvsass.t
    lcdvsass.d
    @0
    eqid
    #
    @1
    eqid
    #
    lcdvsass.k
    lcdvsass.x
    lcdvsass.y
    lcdsmul
    oveq1d
    wph
    cC
    clmod
    wcel
    cX
    @0
    cbs
    cfv
    #
    wcel
    cY
    @8
    wcel
    cG
    cF
    wcel
    @3
    @5
    wceq
    wph
    cC
    cH
    cK
    cW
    lcdvsass.h
    lcdvsass.d
    lcdvsass.k
    lcdlmod
    wph
    cX
    cL
    @8
    lcdvsass.x
    wph
    cC
    @8
    @0
    cU
    cR
    cH
    cK
    cL
    cW
    lcdvsass.h
    lcdvsass.u
    lcdvsass.r
    lcdvsass.l
    lcdvsass.d
    @6
    @8
    eqid
    #
    lcdvsass.k
    lcdsbase
    #
    eleqtrrd
    wph
    cY
    cL
    @8
    lcdvsass.y
    @10
    eleqtrrd
    lcdvsass.g
    cX
    cY
    c.xb
    @1
    @0
    @8
    cF
    cC
    cG
    lcdvsass.f
    @6
    lcdvsass.s
    @9
    @7
    lmodvsass
    syl13anc
    eqtr3d
end
