include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "wn.mm"
include "c1st.mm"
include "cfv.mm"
include "csn.mm"
include "cdm.mm"
include "cuni.mm"
include "c0.mm"
include "1stval.mm"
include "wne.mm"
include "dmsnn0.mm"
include "biimpri.mm"
include "necon1bi.mm"
include "unieqd.mm"
include "uni0.mm"
include "syl6eq.mm"
include "syl5eq.mm"

theorem 1stnpr
  let cA: class A


  assert |- ( -. A e. ( _V X. _V ) -> ( 1st ` A ) = (/) )

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
    c1st
    cfv
    cA
    csn
    cdm
    #
    cuni
    #
    c0
    cA
    1stval
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
    dmsnn0
    biimpri
    necon1bi
    unieqd
    uni0
    syl6eq
    syl5eq
end
