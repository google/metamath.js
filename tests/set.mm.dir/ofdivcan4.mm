include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "cof.mm"
include "simp1.mm"
include "wfn.mm"
include "simp2.mm"
include "ffn.mm"
include "syl.mm"
include "simp3.mm"
include "inidm.mm"
include "offn.mm"
include "wa.mm"
include "eqidd.mm"
include "ofval.mm"
include "wne.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "sylan.mm"
include "eldifsn.mm"
include "sylib.mm"
include "divcan4.mm"
include "3expb.mm"
include "syl2anc.mm"
include "offveq.mm"

theorem ofdivcan4
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ F : A --> CC /\ G : A --> ( CC \ { 0 } ) ) -> ( ( F oF x. G ) oF / G ) = F )

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
    cA
    cc
    cc0
    csn
    cdif
    #
    cG
    wf
    #
    w3a
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    cmul
    co
    #
    @7
    cdiv
    cF
    cG
    cmul
    cof
    co
    cG
    cF
    cV
    @0
    @1
    @3
    simp1
    #
    @4
    cA
    cA
    cmul
    cA
    cF
    cG
    cV
    cV
    @4
    @1
    cF
    cA
    wfn
    @0
    @1
    @3
    simp2
    #
    cA
    cc
    cF
    ffn
    syl
    #
    @4
    @3
    cG
    cA
    wfn
    @0
    @1
    @3
    simp3
    #
    cA
    @2
    cG
    ffn
    syl
    #
    @9
    @9
    cA
    inidm
    #
    offn
    @13
    @11
    @4
    cA
    cA
    @6
    @7
    cmul
    cA
    cF
    cG
    cV
    cV
    @5
    @11
    @13
    @9
    @9
    @14
    @4
    @5
    cA
    wcel
    #
    wa
    #
    @6
    eqidd
    @16
    @7
    eqidd
    #
    ofval
    @17
    @16
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    wa
    #
    @8
    @7
    cdiv
    co
    @6
    wceq
    #
    @4
    @1
    @15
    @18
    @10
    cA
    cc
    @5
    cF
    ffvelrn
    sylan
    @4
    @3
    @15
    @21
    @12
    @3
    @15
    wa
    @7
    @2
    wcel
    @21
    cA
    @2
    @5
    cG
    ffvelrn
    @7
    cc
    cc0
    eldifsn
    sylib
    sylan
    @18
    @19
    @20
    @22
    @6
    @7
    divcan4
    3expb
    syl2anc
    offveq
end
