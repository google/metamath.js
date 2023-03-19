include "cpjh.mm"
include "crn.mm"
include "wcel.mm"
include "cho.mm"
include "ccom.mm"
include "wceq.mm"
include "dfpjop.mm"
include "simplbi.mm"

theorem elpjhmop
  let cT: class T


  assert |- ( T e. ran projh -> T e. HrmOp )

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
    simplbi
end
