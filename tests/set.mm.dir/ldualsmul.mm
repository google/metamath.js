include "co.mm"
include "coppr.mm"
include "cfv.mm"
include "cmulr.mm"
include "eqid.mm"
include "ldualsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "opprmul.mm"
include "syl6eq.mm"

theorem ldualsmul
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ldualsmul.f: |- F = ( Scalar ` W )
  assume ldualsmul.k: |- K = ( Base ` F )
  assume ldualsmul.t: |- .x. = ( .r ` F )
  assume ldualsmul.d: |- D = ( LDual ` W )
  assume ldualsmul.r: |- R = ( Scalar ` D )
  assume ldualsmul.m: |- .xb = ( .r ` R )
  assume ldualsmul.w: |- ( ph -> W e. V )
  assume ldualsmul.x: |- ( ph -> X e. K )
  assume ldualsmul.y: |- ( ph -> Y e. K )


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
    cR
    cmulr
    cfv
    @1
    ldualsmul.m
    wph
    cR
    @0
    cmulr
    wph
    cD
    cR
    cF
    @0
    cW
    cV
    ldualsmul.f
    @0
    eqid
    #
    ldualsmul.d
    ldualsmul.r
    ldualsmul.w
    ldualsca
    fveq2d
    syl5eq
    oveqd
    cK
    cF
    @1
    c.x
    @0
    cX
    cY
    ldualsmul.k
    ldualsmul.t
    @2
    @1
    eqid
    opprmul
    syl6eq
end
