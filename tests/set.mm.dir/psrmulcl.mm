include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "eqid.mm"
include "psrmulcllem.mm"

theorem psrmulcl
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cI: class I
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let vf: setvar f
  assume psrmulcl.s: |- S = ( I mPwSer R )
  assume psrmulcl.b: |- B = ( Base ` S )
  assume psrmulcl.t: |- .x. = ( .r ` S )
  assume psrmulcl.r: |- ( ph -> R e. Ring )
  assume psrmulcl.x: |- ( ph -> X e. B )
  assume psrmulcl.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X .x. Y ) e. B )

  proof
    wph
    cB
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    crab
    #
    cR
    cS
    c.x
    vf
    cI
    cX
    cY
    psrmulcl.s
    psrmulcl.b
    psrmulcl.t
    psrmulcl.r
    psrmulcl.x
    psrmulcl.y
    @0
    eqid
    psrmulcllem
end
