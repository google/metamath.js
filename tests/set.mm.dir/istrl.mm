include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "ctrls.mm"
include "cwlks.mm"
include "trlsfval.mm"
include "wceq.mm"
include "wb.mm"
include "cnveq.mm"
include "funeqd.mm"
include "adantr.mm"
include "relwlk.mm"
include "brfvopabrbr.mm"

theorem istrl
  let cP: class P
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p


  assert |- ( F ( Trails ` G ) P <-> ( F ( Walks ` G ) P /\ Fun `' F ) )

  proof
    vf
    cv
    #
    ccnv
    #
    wfun
    #
    cF
    ccnv
    #
    wfun
    #
    vf
    vp
    ctrls
    cwlks
    cF
    cP
    cG
    vf
    cG
    vp
    trlsfval
    @0
    cF
    wceq
    #
    @2
    @4
    wb
    vp
    cv
    cP
    wceq
    @5
    @1
    @3
    @0
    cF
    cnveq
    funeqd
    adantr
    cG
    relwlk
    brfvopabrbr
end
