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
include "lmodvscl.mm"
include "syl3anc.mm"

theorem lcdvscl
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcdvscl.h: |- H = ( LHyp ` K )
  assume lcdvscl.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvscl.s: |- S = ( Scalar ` U )
  assume lcdvscl.r: |- R = ( Base ` S )
  assume lcdvscl.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvscl.v: |- V = ( Base ` C )
  assume lcdvscl.t: |- .x. = ( .s ` C )
  assume lcdvscl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvscl.x: |- ( ph -> X e. R )
  assume lcdvscl.g: |- ( ph -> G e. V )


  assert |- ( ph -> ( X .x. G ) e. V )

  proof
    wph
    cC
    clmod
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
    cG
    cV
    wcel
    cX
    cG
    c.x
    co
    cV
    wcel
    wph
    cC
    cH
    cK
    cW
    lcdvscl.h
    lcdvscl.c
    lcdvscl.k
    lcdlmod
    wph
    cX
    cR
    @1
    lcdvscl.x
    wph
    cC
    @1
    @0
    cU
    cS
    cH
    cK
    cR
    cW
    lcdvscl.h
    lcdvscl.u
    lcdvscl.s
    lcdvscl.r
    lcdvscl.c
    @0
    eqid
    #
    @1
    eqid
    #
    lcdvscl.k
    lcdsbase
    eleqtrrd
    lcdvscl.g
    cX
    c.x
    @0
    @1
    cV
    cC
    cG
    lcdvscl.v
    @2
    lcdvscl.t
    @3
    lmodvscl
    syl3anc
end
