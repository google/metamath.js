include "co.mm"
include "cfv.mm"
include "cld.mm"
include "cvsca.mm"
include "eqid.mm"
include "lcdvs.mm"
include "oveqd.mm"
include "fveq1d.mm"
include "clfn.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lcdvbaselfl.mm"
include "ldualvsval.mm"
include "eqtrd.mm"

theorem lcdvsval
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcdvsval.h: |- H = ( LHyp ` K )
  assume lcdvsval.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvsval.v: |- V = ( Base ` U )
  assume lcdvsval.s: |- S = ( Scalar ` U )
  assume lcdvsval.r: |- R = ( Base ` S )
  assume lcdvsval.t: |- .x. = ( .r ` S )
  assume lcdvsval.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvsval.f: |- F = ( Base ` C )
  assume lcdvsval.m: |- .xb = ( .s ` C )
  assume lcdvsval.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvsval.x: |- ( ph -> X e. R )
  assume lcdvsval.g: |- ( ph -> G e. F )
  assume lcdvsval.a: |- ( ph -> A e. V )


  assert |- ( ph -> ( ( X .xb G ) ` A ) = ( ( G ` A ) .x. X ) )

  proof
    wph
    cA
    cX
    cG
    c.xb
    co
    #
    cfv
    cA
    cX
    cG
    cU
    cld
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cfv
    cA
    cG
    cfv
    cX
    c.x
    co
    wph
    cA
    @0
    @3
    wph
    c.xb
    @2
    cX
    cG
    wph
    cC
    @1
    c.xb
    @2
    cU
    cH
    cK
    cW
    lcdvsval.h
    lcdvsval.u
    @1
    eqid
    #
    @2
    eqid
    #
    lcdvsval.c
    lcdvsval.m
    lcdvsval.k
    lcdvs
    oveqd
    fveq1d
    wph
    cA
    @1
    cS
    @2
    c.x
    cU
    clfn
    cfv
    #
    cG
    cR
    cV
    cU
    cX
    clmod
    @6
    eqid
    #
    lcdvsval.v
    lcdvsval.s
    lcdvsval.r
    lcdvsval.t
    @4
    @5
    wph
    cU
    cH
    cK
    cW
    lcdvsval.h
    lcdvsval.u
    lcdvsval.k
    dvhlmod
    lcdvsval.x
    wph
    cC
    cU
    @6
    cH
    cK
    cF
    cW
    cG
    lcdvsval.h
    lcdvsval.c
    lcdvsval.f
    lcdvsval.u
    @7
    lcdvsval.k
    lcdvsval.g
    lcdvbaselfl
    lcdvsval.a
    ldualvsval
    eqtrd
end
