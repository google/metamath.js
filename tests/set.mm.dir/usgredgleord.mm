include "cusgr.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cv.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "usgruspgr.mm"
include "uspgredgleord.mm"
include "sylan.mm"

theorem usgredgleord
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume usgredgleord.v: |- V = ( Vtx ` G )
  assume usgredgleord.e: |- E = ( Edg ` G )

  disjoint E e
  disjoint N e
  disjoint E f
  disjoint E x
  disjoint e f
  disjoint e x
  disjoint f x
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint f y
  disjoint x y
  disjoint N f
  disjoint N x
  disjoint N y
  disjoint e y
  disjoint V f
  disjoint V x
  disjoint V y
  assert |- ( ( G e. USGraph /\ N e. V ) -> ( # ` { e e. E | N e. e } ) <_ ( # ` V ) )

  proof
    cG
    cusgr
    wcel
    cG
    cuspgr
    wcel
    cN
    cV
    wcel
    cN
    ve
    cv
    wcel
    ve
    cE
    crab
    chash
    cfv
    cV
    chash
    cfv
    cle
    wbr
    cG
    usgruspgr
    ve
    cE
    cG
    cN
    cV
    usgredgleord.v
    usgredgleord.e
    uspgredgleord
    sylan
end
