include "cpjh.mm"
include "crn.mm"
include "cv.mm"
include "cho.mm"
include "wcel.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "dfpjop.mm"
include "abbi2i.mm"
include "df-rab.mm"
include "eqtr4i.mm"

theorem pjhmopidm
  let vt: setvar t
  let vx: setvar x
  let cT: class T


  assert |- ran projh = { t e. HrmOp | ( t o. t ) = t }

  proof
    cpjh
    crn
    #
    vt
    cv
    #
    cho
    wcel
    @1
    @1
    ccom
    @1
    wceq
    #
    wa
    #
    vt
    cab
    @2
    vt
    cho
    crab
    @3
    vt
    @0
    @1
    dfpjop
    abbi2i
    @2
    vt
    cho
    df-rab
    eqtr4i
end
