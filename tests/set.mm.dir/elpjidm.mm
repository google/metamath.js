include "cpjh.mm"
include "crn.mm"
include "wcel.mm"
include "cho.mm"
include "ccom.mm"
include "wceq.mm"
include "dfpjop.mm"
include "simprbi.mm"

theorem elpjidm
  let cT: class T


  assert |- ( T e. ran projh -> ( T o. T ) = T )

  proof
    cT
    cpjh
    crn
    wcel
    cT
    cho
    wcel
    cT
    cT
    ccom
    cT
    wceq
    cT
    dfpjop
    simprbi
end
