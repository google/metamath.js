include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "cspths.mm"
include "ctrls.mm"
include "spthsfval.mm"
include "wceq.mm"
include "wb.mm"
include "cnveq.mm"
include "funeqd.mm"
include "adantl.mm"
include "reltrls.mm"
include "brfvopabrbr.mm"

theorem isspth
  let cP: class P
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p


  assert |- ( F ( SPaths ` G ) P <-> ( F ( Trails ` G ) P /\ Fun `' P ) )

  proof
    vp
    cv
    #
    ccnv
    #
    wfun
    #
    cP
    ccnv
    #
    wfun
    #
    vf
    vp
    cspths
    ctrls
    cF
    cP
    cG
    vf
    cG
    vp
    spthsfval
    @0
    cP
    wceq
    #
    @2
    @4
    wb
    vf
    cv
    cF
    wceq
    @5
    @1
    @3
    @0
    cP
    cnveq
    funeqd
    adantl
    cG
    reltrls
    brfvopabrbr
end
