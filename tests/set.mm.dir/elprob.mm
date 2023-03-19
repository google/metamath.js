include "cv.mm"
include "cdm.mm"
include "cuni.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cmeas.mm"
include "crn.mm"
include "cprb.mm"
include "id.mm"
include "dmeq.mm"
include "unieqd.mm"
include "fveq12d.mm"
include "eqeq1d.mm"
include "df-prob.mm"
include "elrab2.mm"

theorem elprob
  let cP: class P
  let vp: setvar p


  assert |- ( P e. Prob <-> ( P e. U. ran measures /\ ( P ` U. dom P ) = 1 ) )

  proof
    vp
    cv
    #
    cdm
    #
    cuni
    #
    @0
    cfv
    #
    c1
    wceq
    cP
    cdm
    #
    cuni
    #
    cP
    cfv
    #
    c1
    wceq
    vp
    cP
    cmeas
    crn
    cuni
    cprb
    @0
    cP
    wceq
    #
    @3
    @6
    c1
    @7
    @2
    @5
    @0
    cP
    @7
    id
    @7
    @1
    @4
    @0
    cP
    dmeq
    unieqd
    fveq12d
    eqeq1d
    vp
    df-prob
    elrab2
end
