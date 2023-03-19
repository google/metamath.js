include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "crab.mm"
include "wceq.mm"
include "usgrumgr.mm"
include "nbumgrvtx.mm"
include "sylan.mm"

theorem nbusgrvtx
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let ve: setvar e
  let cX: class X
  let vv: setvar v
  let vx: setvar x
  let cK: class K
  assume nbuhgr.v: |- V = ( Vtx ` G )
  assume nbuhgr.e: |- E = ( Edg ` G )

  disjoint G n
  disjoint N n
  disjoint V n
  disjoint E n
  disjoint E e
  disjoint G e
  disjoint e n
  disjoint N e
  disjoint V e
  disjoint X e
  disjoint X n
  disjoint E v
  disjoint E x
  disjoint n v
  disjoint n x
  disjoint v x
  disjoint G x
  disjoint e x
  disjoint G v
  disjoint N v
  disjoint N x
  disjoint V v
  disjoint V x
  disjoint K n
  disjoint e v
  assert |- ( ( G e. USGraph /\ N e. V ) -> ( G NeighbVtx N ) = { n e. V | { N , n } e. E } )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cN
    cV
    wcel
    cG
    cN
    cnbgr
    co
    cN
    vn
    cv
    cpr
    cE
    wcel
    vn
    cV
    crab
    wceq
    cG
    usgrumgr
    vn
    cE
    cG
    cN
    cV
    nbuhgr.v
    nbuhgr.e
    nbumgrvtx
    sylan
end
