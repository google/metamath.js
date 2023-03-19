include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "cdm.mm"
include "cr.mm"
include "wf.mm"
include "wrel.mm"
include "wb.mm"
include "metf.mm"
include "frel.mm"
include "reldm0.mm"
include "3syl.mm"
include "fdm.mm"
include "syl.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "wo.mm"
include "xpeq0.mm"
include "oridm.mm"
include "bitri.mm"
include "syl6bb.mm"
include "necon3bid.mm"

theorem metn0
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


  assert |- ( D e. ( Met ` X ) -> ( D =/= (/) <-> X =/= (/) ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    c0
    cX
    c0
    @0
    cD
    c0
    wceq
    #
    cX
    cX
    cxp
    #
    c0
    wceq
    #
    cX
    c0
    wceq
    #
    @0
    @1
    cD
    cdm
    #
    c0
    wceq
    #
    @3
    @0
    @2
    cr
    cD
    wf
    #
    cD
    wrel
    @1
    @6
    wb
    cD
    cX
    metf
    #
    @2
    cr
    cD
    frel
    cD
    reldm0
    3syl
    @0
    @5
    @2
    c0
    @0
    @7
    @5
    @2
    wceq
    @8
    @2
    cr
    cD
    fdm
    syl
    eqeq1d
    bitrd
    @3
    @4
    @4
    wo
    @4
    cX
    cX
    xpeq0
    @4
    oridm
    bitri
    syl6bb
    necon3bid
end
