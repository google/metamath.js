include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cxp.mm"
include "cxr.mm"
include "wf.mm"
include "wceq.mm"
include "xmetf.mm"
include "fdm.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6req.mm"

theorem xmetdmdm
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


  assert |- ( D e. ( *Met ` X ) -> X = dom dom D )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cdm
    #
    cdm
    cX
    cX
    cxp
    #
    cdm
    cX
    @0
    @1
    @2
    @0
    @2
    cxr
    cD
    wf
    @1
    @2
    wceq
    cD
    cX
    xmetf
    @2
    cxr
    cD
    fdm
    syl
    dmeqd
    cX
    dmxpid
    syl6req
end
