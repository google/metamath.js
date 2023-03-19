include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cv.mm"
include "wne.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "usgrumgr.mm"
include "umgredg.mm"
include "sylan.mm"

theorem usgredg
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume edgssv2.v: |- V = ( Vtx ` G )
  assume edgssv2.e: |- E = ( Edg ` G )

  disjoint C a
  disjoint C b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint V a
  disjoint V b
  assert |- ( ( G e. USGraph /\ C e. E ) -> E. a e. V E. b e. V ( a =/= b /\ C = { a , b } ) )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cC
    cE
    wcel
    va
    cv
    #
    vb
    cv
    #
    wne
    cC
    @0
    @1
    cpr
    wceq
    wa
    vb
    cV
    wrex
    va
    cV
    wrex
    cG
    usgrumgr
    cC
    cE
    cG
    cV
    va
    vb
    edgssv2.v
    edgssv2.e
    umgredg
    sylan
end
