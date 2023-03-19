include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wn.mm"
include "c2nd.mm"
include "cfv.mm"
include "csn.mm"
include "crn.mm"
include "cuni.mm"
include "c0.mm"
include "2ndval.mm"
include "wne.mm"
include "rnsnn0.mm"
include "biimpri.mm"
include "necon1bi.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem 2ndnpr
  let cA: class A


  assert |- ( -. A e. ( _V X. _V ) -> ( 2nd ` A ) = (/) )

  proof
    cA
    cvv
    cvv
    cxp
    wcel
    #
    wn
    #
    cA
    c2nd
    cfv
    cA
    csn
    crn
    #
    cuni
    #
    c0
    cA
    2ndval
    @1
    @3
    c0
    cuni
    c0
    @1
    @2
    c0
    @0
    @2
    c0
    @0
    @2
    c0
    wne
    cA
    rnsnn0
    biimpri
    necon1bi
    unieqd
    uni0
    syl6eq
    syl5eq
end
