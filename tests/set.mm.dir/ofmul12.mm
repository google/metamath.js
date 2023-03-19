include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cof.mm"
include "simpll.mm"
include "wfn.mm"
include "simplr.mm"
include "ffn.mm"
include "syl.mm"
include "simprl.mm"
include "simprr.mm"
include "inidm.mm"
include "offn.mm"
include "eqidd.mm"
include "ofval.mm"
include "ffvelrnda.mm"
include "mul12d.mm"
include "eqtr4d.mm"
include "offveq.mm"

theorem ofmul12
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vx: setvar x


  assert |- ( ( ( A e. V /\ F : A --> CC ) /\ ( G : A --> CC /\ H : A --> CC ) ) -> ( F oF x. ( G oF x. H ) ) = ( G oF x. ( F oF x. H ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cc
    cF
    wf
    #
    wa
    #
    cA
    cc
    cG
    wf
    #
    cA
    cc
    cH
    wf
    #
    wa
    #
    wa
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @7
    cG
    cfv
    #
    @7
    cH
    cfv
    #
    cmul
    co
    #
    cmul
    cF
    cG
    cH
    cmul
    cof
    #
    co
    cG
    cF
    cH
    @12
    co
    #
    @12
    co
    #
    cV
    @0
    @1
    @5
    simpll
    #
    @6
    @1
    cF
    cA
    wfn
    @0
    @1
    @5
    simplr
    #
    cA
    cc
    cF
    ffn
    syl
    #
    @6
    cA
    cA
    cmul
    cA
    cG
    cH
    cV
    cV
    @6
    @3
    cG
    cA
    wfn
    @2
    @3
    @4
    simprl
    #
    cA
    cc
    cG
    ffn
    syl
    #
    @6
    @4
    cH
    cA
    wfn
    @2
    @3
    @4
    simprr
    #
    cA
    cc
    cH
    ffn
    syl
    #
    @15
    @15
    cA
    inidm
    #
    offn
    @6
    cA
    cA
    cmul
    cA
    cG
    @13
    cV
    cV
    @19
    @6
    cA
    cA
    cmul
    cA
    cF
    cH
    cV
    cV
    @17
    @21
    @15
    @15
    @22
    offn
    #
    @15
    @15
    @22
    offn
    @6
    @7
    cA
    wcel
    wa
    #
    @8
    eqidd
    #
    @6
    cA
    cA
    @9
    @10
    cmul
    cA
    cG
    cH
    cV
    cV
    @7
    @19
    @21
    @15
    @15
    @22
    @24
    @9
    eqidd
    #
    @24
    @10
    eqidd
    #
    ofval
    @24
    @8
    @11
    cmul
    co
    @9
    @8
    @10
    cmul
    co
    #
    cmul
    co
    @7
    @14
    cfv
    @24
    @8
    @9
    @10
    @6
    cA
    cc
    @7
    cF
    @16
    ffvelrnda
    @6
    cA
    cc
    @7
    cG
    @18
    ffvelrnda
    @6
    cA
    cc
    @7
    cH
    @20
    ffvelrnda
    mul12d
    @6
    cA
    cA
    @9
    @28
    cmul
    cA
    cG
    @13
    cV
    cV
    @7
    @19
    @23
    @15
    @15
    @22
    @26
    @6
    cA
    cA
    @8
    @10
    cmul
    cA
    cF
    cH
    cV
    cV
    @7
    @17
    @21
    @15
    @15
    @22
    @25
    @27
    ofval
    ofval
    eqtr4d
    offveq
end
