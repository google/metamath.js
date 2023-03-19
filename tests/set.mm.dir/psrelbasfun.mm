include "wcel.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "wfun.mm"
include "eqid.mm"
include "id.mm"
include "psrelbas.mm"
include "ffun.mm"
include "syl.mm"

theorem psrelbasfun
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let cX: class X
  let vf: setvar f
  assume psrelbasfun.s: |- S = ( I mPwSer R )
  assume psrelbasfun.b: |- B = ( Base ` S )


  assert |- ( X e. B -> Fun X )

  proof
    cX
    cB
    wcel
    #
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
    cbs
    cfv
    #
    cX
    wf
    cX
    wfun
    @0
    cB
    @1
    cR
    cS
    vf
    cI
    @2
    cX
    psrelbasfun.s
    @2
    eqid
    @1
    eqid
    psrelbasfun.b
    @0
    id
    psrelbas
    @1
    @2
    cX
    ffun
    syl
end
