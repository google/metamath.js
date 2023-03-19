include "cpths.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "c1.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cpr.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "ispth.mm"
include "simp1bi.mm"

theorem pthistrl
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Paths ` G ) P -> F ( Trails ` G ) P )

  proof
    cF
    cP
    cG
    cpths
    cfv
    wbr
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cP
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    cres
    ccnv
    wfun
    cP
    cc0
    @0
    cpr
    cima
    cP
    @1
    cima
    cin
    c0
    wceq
    cP
    cF
    cG
    ispth
    simp1bi
end
