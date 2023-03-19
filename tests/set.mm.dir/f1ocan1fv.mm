include "wfun.mm"
include "wf1o.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnv.mm"
include "cfv.mm"
include "ccom.mm"
include "wf.mm"
include "wceq.mm"
include "f1of.mm"
include "3ad2ant2.mm"
include "f1ocnv.mm"
include "syl.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "f1ocnvfv2.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem f1ocan1fv
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cX: class X


  assert |- ( ( Fun F /\ G : A -1-1-onto-> B /\ X e. B ) -> ( ( F o. G ) ` ( `' G ` X ) ) = ( F ` X ) )

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
    cB
    wcel
    #
    w3a
    #
    cX
    cG
    ccnv
    #
    cfv
    #
    cF
    cG
    ccom
    cfv
    #
    @5
    cG
    cfv
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    @3
    cA
    cB
    cG
    wf
    #
    @5
    cA
    wcel
    @6
    @8
    wceq
    @1
    @0
    @9
    @2
    cA
    cB
    cG
    f1of
    3ad2ant2
    @3
    cB
    cA
    cX
    @4
    @1
    @0
    cB
    cA
    @4
    wf
    #
    @2
    @1
    cB
    cA
    @4
    wf1o
    @10
    cA
    cB
    cG
    f1ocnv
    cB
    cA
    @4
    f1of
    syl
    3ad2ant2
    @0
    @1
    @2
    simp3
    ffvelrnd
    cA
    cB
    @5
    cF
    cG
    fvco3
    syl2anc
    @3
    @7
    cX
    cF
    @1
    @2
    @7
    cX
    wceq
    @0
    cA
    cB
    cX
    cG
    f1ocnvfv2
    3adant1
    fveq2d
    eqtrd
end
