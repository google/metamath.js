include "cminusg.mm"
include "cfv.mm"
include "coppr.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualsca.mm"
include "fveq2d.mm"
include "opprneg.mm"
include "3eqtr4g.mm"

theorem ldualneg
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let cM: class M
  let cN: class N
  let cW: class W
  assume ldualneg.r: |- R = ( Scalar ` W )
  assume ldualneg.m: |- M = ( invg ` R )
  assume ldualneg.d: |- D = ( LDual ` W )
  assume ldualneg.s: |- S = ( Scalar ` D )
  assume ldualneg.n: |- N = ( invg ` S )
  assume ldualneg.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> N = M )

  proof
    wph
    cS
    cminusg
    cfv
    cR
    coppr
    cfv
    #
    cminusg
    cfv
    cN
    cM
    wph
    cS
    @0
    cminusg
    wph
    cD
    cS
    cR
    @0
    cW
    clmod
    ldualneg.r
    @0
    eqid
    #
    ldualneg.d
    ldualneg.s
    ldualneg.w
    ldualsca
    fveq2d
    ldualneg.n
    cR
    cM
    @0
    @1
    ldualneg.m
    opprneg
    3eqtr4g
end
