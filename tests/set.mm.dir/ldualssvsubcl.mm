include "clmod.mm"
include "wcel.mm"
include "co.mm"
include "lduallmod.mm"
include "lssvsubcl.mm"
include "syl22anc.mm"

theorem ldualssvsubcl
  let wph: wff ph
  let cD: class D
  let cS: class S
  let cU: class U
  let c.mi: class .-
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ldualssvsubcl.d: |- D = ( LDual ` W )
  assume ldualssvsubcl.m: |- .- = ( -g ` D )
  assume ldualssvsubcl.s: |- S = ( LSubSp ` D )
  assume ldualssvsubcl.w: |- ( ph -> W e. LMod )
  assume ldualssvsubcl.u: |- ( ph -> U e. S )
  assume ldualssvsubcl.x: |- ( ph -> X e. U )
  assume ldualssvsubcl.y: |- ( ph -> Y e. U )


  assert |- ( ph -> ( X .- Y ) e. U )

  proof
    wph
    cD
    clmod
    wcel
    cU
    cS
    wcel
    cX
    cU
    wcel
    cY
    cU
    wcel
    cX
    cY
    c.mi
    co
    cU
    wcel
    wph
    cD
    cW
    ldualssvsubcl.d
    ldualssvsubcl.w
    lduallmod
    ldualssvsubcl.u
    ldualssvsubcl.x
    ldualssvsubcl.y
    cS
    cU
    c.mi
    cD
    cX
    cY
    ldualssvsubcl.m
    ldualssvsubcl.s
    lssvsubcl
    syl22anc
end
