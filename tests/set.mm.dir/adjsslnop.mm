include "cado.mm"
include "cdm.mm"
include "clo.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "adjadj.mm"
include "dmadjrn.mm"
include "adjlnop.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "ssriv.mm"

theorem adjsslnop
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T


  assert |- dom adjh C_ LinOp

  proof
    vt
    cado
    cdm
    #
    clo
    vt
    cv
    #
    @0
    wcel
    #
    @1
    cado
    cfv
    #
    cado
    cfv
    #
    @1
    clo
    @1
    adjadj
    @2
    @3
    @0
    wcel
    @4
    clo
    wcel
    @1
    dmadjrn
    @3
    adjlnop
    syl
    eqeltrrd
    ssriv
end
