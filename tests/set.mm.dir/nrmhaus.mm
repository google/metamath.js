include "cnrm.mm"
include "wcel.mm"
include "cha.mm"
include "ct1.mm"
include "haust1.mm"
include "creg.mm"
include "nrmreg.mm"
include "ex.mm"
include "ct0.mm"
include "t1t0.mm"
include "reghaus.mm"
include "syl5ibrcom.mm"
include "sylcom.mm"
include "impbid2.mm"

theorem nrmhaus
  let cJ: class J


  assert |- ( J e. Nrm -> ( J e. Haus <-> J e. Fre ) )

  proof
    cJ
    cnrm
    wcel
    #
    cJ
    cha
    wcel
    #
    cJ
    ct1
    wcel
    #
    cJ
    haust1
    @0
    @2
    cJ
    creg
    wcel
    #
    @1
    @0
    @2
    @3
    cJ
    nrmreg
    ex
    @2
    @1
    @3
    cJ
    ct0
    wcel
    cJ
    t1t0
    cJ
    reghaus
    syl5ibrcom
    sylcom
    impbid2
end
