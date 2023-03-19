include "cv.mm"
include "cfv.mm"
include "cale.mm"
include "crn.mm"
include "wcel.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "alephfplem1.mm"
include "com.mm"
include "con0.mm"
include "wfn.mm"
include "alephfnon.mm"
include "alephsson.mm"
include "sseli.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "alephfplem2.mm"
include "syl5ibr.mm"
include "finds1.mm"

theorem alephfplem3
  let vv: setvar v
  let cH: class H
  let vw: setvar w
  let vz: setvar z
  assume alephfplem.1: |- H = ( rec ( aleph , _om ) |` _om )

  disjoint H v
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint H z
  disjoint H w
  assert |- ( v e. _om -> ( H ` v ) e. ran aleph )

  proof
    vv
    cv
    #
    cH
    cfv
    #
    cale
    crn
    #
    wcel
    c0
    cH
    cfv
    #
    @2
    wcel
    vw
    cv
    #
    cH
    cfv
    #
    @2
    wcel
    #
    @4
    csuc
    #
    cH
    cfv
    #
    @2
    wcel
    #
    vv
    vw
    @0
    c0
    wceq
    @1
    @3
    @2
    @0
    c0
    cH
    fveq2
    eleq1d
    @0
    @4
    wceq
    @1
    @5
    @2
    @0
    @4
    cH
    fveq2
    eleq1d
    @0
    @7
    wceq
    @1
    @8
    @2
    @0
    @7
    cH
    fveq2
    eleq1d
    cH
    alephfplem.1
    alephfplem1
    @6
    @9
    @4
    com
    wcel
    #
    @5
    cale
    cfv
    #
    @2
    wcel
    #
    @6
    cale
    con0
    wfn
    @5
    con0
    wcel
    @12
    alephfnon
    @2
    con0
    @5
    alephsson
    sseli
    con0
    @5
    cale
    fnfvelrn
    sylancr
    @10
    @8
    @11
    @2
    vw
    cH
    alephfplem.1
    alephfplem2
    eleq1d
    syl5ibr
    finds1
end
