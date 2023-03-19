include "co.mm"
include "cfv.mm"
include "cld.mm"
include "cplusg.mm"
include "eqid.mm"
include "lcdvadd.mm"
include "oveqd.mm"
include "fveq1d.mm"
include "clfn.mm"
include "dvhlmod.mm"
include "lcdvbaselfl.mm"
include "ldualvaddval.mm"
include "eqtrd.mm"

theorem lcdvaddval
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume lcdvaddval.h: |- H = ( LHyp ` K )
  assume lcdvaddval.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvaddval.v: |- V = ( Base ` U )
  assume lcdvaddval.r: |- R = ( Scalar ` U )
  assume lcdvaddval.a: |- .+ = ( +g ` R )
  assume lcdvaddval.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvaddval.d: |- D = ( Base ` C )
  assume lcdvaddval.p: |- .+b = ( +g ` C )
  assume lcdvaddval.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvaddval.f: |- ( ph -> F e. D )
  assume lcdvaddval.g: |- ( ph -> G e. D )
  assume lcdvaddval.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( F .+b G ) ` X ) = ( ( F ` X ) .+ ( G ` X ) ) )

  proof
    wph
    cX
    cF
    cG
    c.pb
    co
    #
    cfv
    cX
    cF
    cG
    cU
    cld
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cfv
    cX
    cF
    cfv
    cX
    cG
    cfv
    c.pl
    co
    wph
    cX
    @0
    @3
    wph
    c.pb
    @2
    cF
    cG
    wph
    cC
    @1
    @2
    c.pb
    cU
    cH
    cK
    cW
    lcdvaddval.h
    lcdvaddval.u
    @1
    eqid
    #
    @2
    eqid
    #
    lcdvaddval.c
    lcdvaddval.p
    lcdvaddval.k
    lcdvadd
    oveqd
    fveq1d
    wph
    @1
    c.pl
    @2
    cR
    cU
    clfn
    cfv
    #
    cF
    cG
    cV
    cU
    cX
    lcdvaddval.v
    lcdvaddval.r
    lcdvaddval.a
    @6
    eqid
    #
    @4
    @5
    wph
    cU
    cH
    cK
    cW
    lcdvaddval.h
    lcdvaddval.u
    lcdvaddval.k
    dvhlmod
    wph
    cC
    cU
    @6
    cH
    cK
    cD
    cW
    cF
    lcdvaddval.h
    lcdvaddval.c
    lcdvaddval.d
    lcdvaddval.u
    @7
    lcdvaddval.k
    lcdvaddval.f
    lcdvbaselfl
    wph
    cC
    cU
    @6
    cH
    cK
    cD
    cW
    cG
    lcdvaddval.h
    lcdvaddval.c
    lcdvaddval.d
    lcdvaddval.u
    @7
    lcdvaddval.k
    lcdvaddval.g
    lcdvbaselfl
    lcdvaddval.x
    ldualvaddval
    eqtrd
end
