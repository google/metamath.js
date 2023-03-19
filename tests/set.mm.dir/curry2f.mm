include "cxp.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "fovrn.mm"
include "3com23.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "wfn.mm"
include "wceq.mm"
include "ffn.mm"
include "curry2.mm"
include "sylan.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem curry2f
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vx: setvar x
  assume curry2.1: |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) )


  assert |- ( ( F : ( A X. B ) --> D /\ C e. B ) -> G : A --> D )

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
    cB
    wcel
    #
    wa
    #
    cA
    cD
    cG
    wf
    cA
    cD
    vx
    cA
    vx
    cv
    #
    cC
    cF
    co
    #
    cmpt
    #
    wf
    @3
    vx
    cA
    @5
    cD
    @6
    @1
    @2
    @4
    cA
    wcel
    #
    @5
    cD
    wcel
    #
    @1
    @7
    @2
    @8
    @4
    cC
    cD
    cA
    cB
    cF
    fovrn
    3com23
    3expa
    @6
    eqid
    fmptd
    @3
    cA
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
    curry2.1
    curry2
    sylan
    feq1d
    mpbird
end
