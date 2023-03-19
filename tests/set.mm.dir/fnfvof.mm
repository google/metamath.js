include "wfn.mm"
include "wa.mm"
include "wcel.mm"
include "cof.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "anasss.mm"

theorem fnfvof
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X


  assert |- ( ( ( F Fn A /\ G Fn A ) /\ ( A e. V /\ X e. A ) ) -> ( ( F oF R G ) ` X ) = ( ( F ` X ) R ( G ` X ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    wa
    #
    cA
    cV
    wcel
    #
    cX
    cA
    wcel
    #
    cX
    cF
    cG
    cR
    cof
    co
    cfv
    cX
    cF
    cfv
    #
    cX
    cG
    cfv
    #
    cR
    co
    wceq
    @2
    @3
    wa
    #
    cA
    cA
    @5
    @6
    cR
    cA
    cF
    cG
    cV
    cV
    cX
    @0
    @1
    @3
    simpll
    @0
    @1
    @3
    simplr
    @2
    @3
    simpr
    #
    @8
    cA
    inidm
    @7
    @4
    wa
    #
    @5
    eqidd
    @9
    @6
    eqidd
    ofval
    anasss
end
