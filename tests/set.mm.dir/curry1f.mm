include "cxp.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "fovrn.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "curry1.mm"
include "sylan.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem curry1f
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume curry1.1: |- G = ( F o. `' ( 2nd |` ( { C } X. _V ) ) )


  assert |- ( ( F : ( A X. B ) --> D /\ C e. A ) -> G : B --> D )

  proof
    cA
    cB
    cxp
    #
    cD
    cF
    wf
    #
    cC
    cA
    wcel
    #
    wa
    #
    cB
    cD
    cG
    wf
    cB
    cD
    vx
    cB
    cC
    vx
    cv
    #
    cF
    co
    #
    cmpt
    #
    wf
    @3
    vx
    cB
    @5
    cD
    @6
    @1
    @2
    @4
    cB
    wcel
    @5
    cD
    wcel
    cC
    @4
    cD
    cA
    cB
    cF
    fovrn
    3expa
    @6
    eqid
    fmptd
    @3
    cB
    cD
    cG
    @6
    @1
    cF
    @0
    wfn
    @2
    cG
    @6
    wceq
    @0
    cD
    cF
    ffn
    vx
    cA
    cB
    cC
    cF
    cG
    curry1.1
    curry1
    sylan
    feq1d
    mpbird
end
