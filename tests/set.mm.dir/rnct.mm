include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ccnv.mm"
include "cdm.mm"
include "crn.mm"
include "cnvct.mm"
include "dmct.mm"
include "df-rn.mm"
include "breq1i.mm"
include "biimpri.mm"
include "3syl.mm"

theorem rnct
  let cA: class A


  assert |- ( A ~<_ _om -> ran A ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    cA
    ccnv
    #
    com
    cdom
    wbr
    @0
    cdm
    #
    com
    cdom
    wbr
    #
    cA
    crn
    #
    com
    cdom
    wbr
    #
    cA
    cnvct
    @0
    dmct
    @4
    @2
    @3
    @1
    com
    cdom
    cA
    df-rn
    breq1i
    biimpri
    3syl
end
