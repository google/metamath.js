include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctpos.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "xmetsym.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "xmetf.mm"
include "ffn.mm"
include "tpossym.mm"
include "3syl.mm"
include "mpbird.mm"

theorem xmettpos
  let cD: class D
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cR: class R
  let cC: class C


  assert |- ( D e. ( *Met ` X ) -> tpos D = D )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    ctpos
    cD
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    @3
    @2
    cD
    co
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @0
    @4
    vx
    vy
    cX
    cX
    @0
    @2
    cX
    wcel
    @3
    cX
    wcel
    @4
    @2
    @3
    cD
    cX
    xmetsym
    3expb
    ralrimivva
    @0
    cX
    cX
    cxp
    #
    cxr
    cD
    wf
    cD
    @6
    wfn
    @1
    @5
    wb
    cD
    cX
    xmetf
    @6
    cxr
    cD
    ffn
    vx
    vy
    cX
    cD
    tpossym
    3syl
    mpbird
end
