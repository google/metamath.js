include "cbs.mm"
include "cfv.mm"
include "coppr.mm"
include "eqid.mm"
include "ldualsca.mm"
include "fveq2d.mm"
include "opprbas.mm"
include "3eqtr4g.mm"

theorem ldualsbase
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cF: class F
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  assume ldualsbase.f: |- F = ( Scalar ` W )
  assume ldualsbase.l: |- L = ( Base ` F )
  assume ldualsbase.d: |- D = ( LDual ` W )
  assume ldualsbase.r: |- R = ( Scalar ` D )
  assume ldualsbase.k: |- K = ( Base ` R )
  assume ldualsbase.w: |- ( ph -> W e. V )


  assert |- ( ph -> K = L )

  proof
    wph
    cR
    cbs
    cfv
    cF
    coppr
    cfv
    #
    cbs
    cfv
    cK
    cL
    wph
    cR
    @0
    cbs
    wph
    cD
    cR
    cF
    @0
    cW
    cV
    ldualsbase.f
    @0
    eqid
    #
    ldualsbase.d
    ldualsbase.r
    ldualsbase.w
    ldualsca
    fveq2d
    ldualsbase.k
    cL
    cF
    @0
    @1
    ldualsbase.l
    opprbas
    3eqtr4g
end
