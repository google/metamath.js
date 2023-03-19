include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cmetid.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "copab.mm"
include "cxp.mm"
include "metidval.mm"
include "opabssxp.mm"
include "syl6eqss.mm"

theorem metidss
  let cD: class D
  let cX: class X
  let vd: setvar d
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( D e. ( PsMet ` X ) -> ( ~Met ` D ) C_ ( X X. X ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    cD
    cmetid
    cfv
    vx
    cv
    #
    cX
    wcel
    vy
    cv
    #
    cX
    wcel
    wa
    @0
    @1
    cD
    co
    cc0
    wceq
    #
    wa
    vx
    vy
    copab
    cX
    cX
    cxp
    vx
    vy
    cD
    cX
    metidval
    @2
    vx
    vy
    cX
    cX
    opabssxp
    syl6eqss
end
