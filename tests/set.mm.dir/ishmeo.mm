include "cv.mm"
include "ccnv.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "chmeo.mm"
include "wceq.mm"
include "cnveq.mm"
include "eleq1d.mm"
include "hmeofval.mm"
include "elrab2.mm"

theorem ishmeo
  let cF: class F
  let cJ: class J
  let cK: class K
  let vf: setvar f


  assert |- ( F e. ( J Homeo K ) <-> ( F e. ( J Cn K ) /\ `' F e. ( K Cn J ) ) )

  proof
    vf
    cv
    #
    ccnv
    #
    cK
    cJ
    ccn
    co
    #
    wcel
    cF
    ccnv
    #
    @2
    wcel
    vf
    cF
    cJ
    cK
    ccn
    co
    cJ
    cK
    chmeo
    co
    @0
    cF
    wceq
    @1
    @3
    @2
    @0
    cF
    cnveq
    eleq1d
    vf
    cJ
    cK
    hmeofval
    elrab2
end
