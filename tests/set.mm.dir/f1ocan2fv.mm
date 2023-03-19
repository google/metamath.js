include "wfun.mm"
include "wf1o.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnv.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "wrel.mm"
include "f1orel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "3ad2ant2.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "f1ocnv.mm"
include "f1ocan1fv.mm"
include "syl3an2.mm"
include "eqtr3d.mm"

theorem f1ocan2fv
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cX: class X


  assert |- ( ( Fun F /\ G : A -1-1-onto-> B /\ X e. A ) -> ( ( F o. `' G ) ` ( G ` X ) ) = ( F ` X ) )

  proof
    cF
    wfun
    #
    cA
    cB
    cG
    wf1o
    #
    cX
    cA
    wcel
    #
    w3a
    #
    cX
    cG
    ccnv
    #
    ccnv
    #
    cfv
    #
    cF
    @4
    ccom
    #
    cfv
    #
    cX
    cG
    cfv
    #
    @7
    cfv
    cX
    cF
    cfv
    #
    @3
    @6
    @9
    @7
    @3
    cX
    @5
    cG
    @1
    @0
    @5
    cG
    wceq
    #
    @2
    @1
    cG
    wrel
    @11
    cA
    cB
    cG
    f1orel
    cG
    dfrel2
    sylib
    3ad2ant2
    fveq1d
    fveq2d
    @1
    @0
    cB
    cA
    @4
    wf1o
    @2
    @8
    @10
    wceq
    cA
    cB
    cG
    f1ocnv
    cB
    cA
    cF
    @4
    cX
    f1ocan1fv
    syl3an2
    eqtr3d
end
