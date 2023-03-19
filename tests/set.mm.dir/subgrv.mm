include "csubgr.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "relsubgr.mm"
include "brrelexi.mm"
include "brrelex2i.mm"
include "jca.mm"

theorem subgrv
  let cS: class S
  let cG: class G


  assert |- ( S SubGraph G -> ( S e. _V /\ G e. _V ) )

  proof
    cS
    cG
    csubgr
    wbr
    cS
    cvv
    wcel
    cG
    cvv
    wcel
    cS
    cG
    csubgr
    relsubgr
    brrelexi
    cS
    cG
    csubgr
    relsubgr
    brrelex2i
    jca
end
