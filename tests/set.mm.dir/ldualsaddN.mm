include "cplusg.mm"
include "cfv.mm"
include "coppr.mm"
include "eqid.mm"
include "ldualsca.mm"
include "fveq2d.mm"
include "oppradd.mm"
include "3eqtr4g.mm"

theorem ldualsaddN
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  assume ldualsadd.f: |- F = ( Scalar ` W )
  assume ldualsadd.q: |- .+ = ( +g ` F )
  assume ldualsadd.d: |- D = ( LDual ` W )
  assume ldualsadd.r: |- R = ( Scalar ` D )
  assume ldualsadd.p: |- .+b = ( +g ` R )
  assume ldualsadd.w: |- ( ph -> W e. V )


  assert |- ( ph -> .+b = .+ )

  proof
    wph
    cR
    cplusg
    cfv
    cF
    coppr
    cfv
    #
    cplusg
    cfv
    c.pb
    c.pl
    wph
    cR
    @0
    cplusg
    wph
    cD
    cR
    cF
    @0
    cW
    cV
    ldualsadd.f
    @0
    eqid
    #
    ldualsadd.d
    ldualsadd.r
    ldualsadd.w
    ldualsca
    fveq2d
    ldualsadd.p
    c.pl
    cF
    @0
    @1
    ldualsadd.q
    oppradd
    3eqtr4g
end
