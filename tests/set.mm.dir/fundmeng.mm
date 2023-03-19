include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "funeq.mm"
include "dmeq.mm"
include "id.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vex.mm"
include "fundmen.mm"
include "vtoclg.mm"
include "imp.mm"

theorem fundmeng
  let cF: class F
  let cV: class V
  let cA: class A
  let vx: setvar x


  assert |- ( ( F e. V /\ Fun F ) -> dom F ~~ F )

  proof
    cF
    cV
    wcel
    cF
    wfun
    #
    cF
    cdm
    #
    cF
    cen
    wbr
    #
    vx
    cv
    #
    wfun
    #
    @3
    cdm
    #
    @3
    cen
    wbr
    #
    wi
    @0
    @2
    wi
    vx
    cF
    cV
    @3
    cF
    wceq
    #
    @4
    @0
    @6
    @2
    @3
    cF
    funeq
    @7
    @5
    @1
    @3
    cF
    cen
    @3
    cF
    dmeq
    @7
    id
    breq12d
    imbi12d
    @3
    vx
    vex
    fundmen
    vtoclg
    imp
end
