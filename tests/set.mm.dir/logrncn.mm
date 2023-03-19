include "clog.mm"
include "crn.mm"
include "wcel.mm"
include "cc.mm"
include "cpi.mm"
include "cneg.mm"
include "cim.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "ellogrn.mm"
include "simp1bi.mm"

theorem logrncn
  let cA: class A


  assert |- ( A e. ran log -> A e. CC )

  proof
    cA
    clog
    crn
    wcel
    cA
    cc
    wcel
    cpi
    cneg
    cA
    cim
    cfv
    #
    clt
    wbr
    @0
    cpi
    cle
    wbr
    cA
    ellogrn
    simp1bi
end
