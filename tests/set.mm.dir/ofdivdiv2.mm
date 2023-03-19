include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "cdiv.mm"
include "cof.mm"
include "co.mm"
include "cmul.mm"
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
include "wne.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "sylan.mm"
include "eldifsn.mm"
include "sylib.mm"
include "divdiv2.mm"
include "syl3anc.mm"
include "ofval.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "offveq.mm"

theorem ofdivdiv2
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let vx: setvar x


  assert |- ( ( ( A e. V /\ F : A --> CC ) /\ ( G : A --> ( CC \ { 0 } ) /\ H : A --> ( CC \ { 0 } ) ) ) -> ( F oF / ( G oF / H ) ) = ( ( F oF x. H ) oF / G ) )

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
    cc0
    csn
    cdif
    #
    cG
    wf
    #
    cA
    @3
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
    @8
    cG
    cH
    cdiv
    cof
    #
    co
    #
    cfv
    #
    cdiv
    cF
    @11
    cF
    cH
    cmul
    cof
    co
    #
    cG
    @10
    co
    #
    cV
    @0
    @1
    @6
    simpll
    #
    @7
    @1
    cF
    cA
    wfn
    @0
    @1
    @6
    simplr
    #
    cA
    cc
    cF
    ffn
    syl
    #
    @7
    cA
    cA
    cdiv
    cA
    cG
    cH
    cV
    cV
    @7
    @4
    cG
    cA
    wfn
    @2
    @4
    @5
    simprl
    #
    cA
    @3
    cG
    ffn
    syl
    #
    @7
    @5
    cH
    cA
    wfn
    @2
    @4
    @5
    simprr
    #
    cA
    @3
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
    @7
    cA
    cA
    cdiv
    cA
    @13
    cG
    cV
    cV
    @7
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
    @19
    @15
    @15
    @22
    offn
    @7
    @8
    cA
    wcel
    #
    wa
    #
    @9
    eqidd
    #
    @25
    @12
    eqidd
    @25
    @9
    @8
    cG
    cfv
    #
    @8
    cH
    cfv
    #
    cdiv
    co
    #
    cdiv
    co
    #
    @9
    @28
    cmul
    co
    #
    @27
    cdiv
    co
    #
    @9
    @12
    cdiv
    co
    @8
    @14
    cfv
    @25
    @9
    cc
    wcel
    #
    @27
    cc
    wcel
    @27
    cc0
    wne
    wa
    #
    @28
    cc
    wcel
    @28
    cc0
    wne
    wa
    #
    @30
    @32
    wceq
    @7
    @1
    @24
    @33
    @16
    cA
    cc
    @8
    cF
    ffvelrn
    sylan
    @7
    @4
    @24
    @34
    @18
    @4
    @24
    wa
    @27
    @3
    wcel
    @34
    cA
    @3
    @8
    cG
    ffvelrn
    @27
    cc
    cc0
    eldifsn
    sylib
    sylan
    @7
    @5
    @24
    @35
    @20
    @5
    @24
    wa
    @28
    @3
    wcel
    @35
    cA
    @3
    @8
    cH
    ffvelrn
    @28
    cc
    cc0
    eldifsn
    sylib
    sylan
    @9
    @27
    @28
    divdiv2
    syl3anc
    @25
    @12
    @29
    @9
    cdiv
    @7
    cA
    cA
    @27
    @28
    cdiv
    cA
    cG
    cH
    cV
    cV
    @8
    @19
    @21
    @15
    @15
    @22
    @25
    @27
    eqidd
    #
    @25
    @28
    eqidd
    #
    ofval
    oveq2d
    @7
    cA
    cA
    @31
    @27
    cdiv
    cA
    @13
    cG
    cV
    cV
    @8
    @23
    @19
    @15
    @15
    @22
    @7
    cA
    cA
    @9
    @28
    cmul
    cA
    cF
    cH
    cV
    cV
    @8
    @17
    @21
    @15
    @15
    @22
    @26
    @37
    ofval
    @36
    ofval
    3eqtr4d
    offveq
end
