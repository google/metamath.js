include "clcd.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "hdmapcl.mm"
include "lcdvbasecl.mm"

theorem hdmapipcl
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume hdmapipcl.h: |- H = ( LHyp ` K )
  assume hdmapipcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapipcl.v: |- V = ( Base ` U )
  assume hdmapipcl.r: |- R = ( Scalar ` U )
  assume hdmapipcl.b: |- B = ( Base ` R )
  assume hdmapipcl.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapipcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapipcl.x: |- ( ph -> X e. V )
  assume hdmapipcl.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( S ` Y ) ` X ) e. B )

  proof
    wph
    cW
    cK
    clcd
    cfv
    cfv
    #
    cB
    cR
    cU
    @0
    cbs
    cfv
    #
    cY
    cS
    cfv
    cH
    cK
    cV
    cW
    cX
    hdmapipcl.h
    hdmapipcl.u
    hdmapipcl.v
    hdmapipcl.r
    hdmapipcl.b
    @0
    eqid
    #
    @1
    eqid
    #
    hdmapipcl.k
    wph
    @0
    @1
    cS
    cY
    cU
    cH
    cK
    cV
    cW
    hdmapipcl.h
    hdmapipcl.u
    hdmapipcl.v
    @2
    @3
    hdmapipcl.s
    hdmapipcl.k
    hdmapipcl.y
    hdmapcl
    hdmapipcl.x
    lcdvbasecl
end
