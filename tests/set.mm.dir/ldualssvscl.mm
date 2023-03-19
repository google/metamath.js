include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "co.mm"
include "lduallmod.mm"
include "eqid.mm"
include "ldualsbase.mm"
include "eleqtrrd.mm"
include "lssvscl.mm"
include "syl22anc.mm"

theorem ldualssvscl
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ldualssvscl.r: |- R = ( Scalar ` W )
  assume ldualssvscl.k: |- K = ( Base ` R )
  assume ldualssvscl.d: |- D = ( LDual ` W )
  assume ldualssvscl.t: |- .x. = ( .s ` D )
  assume ldualssvscl.s: |- S = ( LSubSp ` D )
  assume ldualssvscl.w: |- ( ph -> W e. LMod )
  assume ldualssvscl.u: |- ( ph -> U e. S )
  assume ldualssvscl.x: |- ( ph -> X e. K )
  assume ldualssvscl.y: |- ( ph -> Y e. U )


  assert |- ( ph -> ( X .x. Y ) e. U )

  proof
    wph
    cD
    clmod
    wcel
    cU
    cS
    wcel
    cX
    cD
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    cY
    cU
    wcel
    cX
    cY
    c.x
    co
    cU
    wcel
    wph
    cD
    cW
    ldualssvscl.d
    ldualssvscl.w
    lduallmod
    ldualssvscl.u
    wph
    cX
    cK
    @1
    ldualssvscl.x
    wph
    cD
    @0
    cR
    @1
    cK
    clmod
    cW
    ldualssvscl.r
    ldualssvscl.k
    ldualssvscl.d
    @0
    eqid
    #
    @1
    eqid
    #
    ldualssvscl.w
    ldualsbase
    eleqtrrd
    ldualssvscl.y
    @1
    cS
    c.x
    cU
    @0
    cD
    cX
    cY
    @2
    ldualssvscl.t
    @3
    ldualssvscl.s
    lssvscl
    syl22anc
end
