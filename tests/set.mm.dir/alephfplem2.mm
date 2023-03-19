include "cv.mm"
include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cale.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "frsuc.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem alephfplem2
  let vw: setvar w
  let cH: class H
  let vz: setvar z
  let vv: setvar v
  assume alephfplem.1: |- H = ( rec ( aleph , _om ) |` _om )

  disjoint H w
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint H z
  disjoint H v
  assert |- ( w e. _om -> ( H ` suc w ) = ( aleph ` ( H ` w ) ) )

  proof
    vw
    cv
    #
    com
    wcel
    @0
    csuc
    #
    cale
    com
    crdg
    com
    cres
    #
    cfv
    @0
    @2
    cfv
    #
    cale
    cfv
    @1
    cH
    cfv
    @0
    cH
    cfv
    #
    cale
    cfv
    com
    @0
    cale
    frsuc
    @1
    cH
    @2
    alephfplem.1
    fveq1i
    @4
    @3
    cale
    @0
    cH
    @2
    alephfplem.1
    fveq1i
    fveq2i
    3eqtr4g
end
