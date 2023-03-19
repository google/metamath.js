include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "cxp.mm"
include "cof.mm"
include "simp1.mm"
include "wfn.mm"
include "simp2.mm"
include "ffn.mm"
include "syl.mm"
include "ax-1cn.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "simp3.mm"
include "inidm.mm"
include "offn.mm"
include "wa.mm"
include "eqidd.mm"
include "1cnd.mm"
include "ofc1.mm"
include "wne.mm"
include "wceq.mm"
include "ffvelrn.mm"
include "sylan.mm"
include "eldifsn.mm"
include "sylib.mm"
include "divrec.mm"
include "eqcomd.mm"
include "3expb.mm"
include "syl2anc.mm"
include "ofval.mm"
include "eqtr4d.mm"
include "offveq.mm"

theorem ofdivrec
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ F : A --> CC /\ G : A --> ( CC \ { 0 } ) ) -> ( F oF x. ( ( A X. { 1 } ) oF / G ) ) = ( F oF / G ) )

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
    c1
    @5
    cG
    cfv
    #
    cdiv
    co
    #
    cmul
    cF
    cA
    c1
    csn
    cxp
    #
    cG
    cdiv
    cof
    #
    co
    cF
    cG
    @10
    co
    #
    cV
    @0
    @1
    @3
    simp1
    #
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
    cA
    cA
    cdiv
    cA
    @9
    cG
    cV
    cV
    c1
    cc
    wcel
    @9
    cA
    wfn
    @4
    ax-1cn
    cA
    c1
    cc
    fnconstg
    mp1i
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
    @12
    @12
    cA
    inidm
    #
    offn
    @4
    cA
    cA
    cdiv
    cA
    cF
    cG
    cV
    cV
    @14
    @16
    @12
    @12
    @17
    offn
    @4
    @5
    cA
    wcel
    #
    wa
    #
    @6
    eqidd
    #
    @4
    cA
    c1
    @7
    cdiv
    cG
    cV
    cc
    @5
    @12
    @4
    1cnd
    @16
    @19
    @7
    eqidd
    #
    ofc1
    @19
    @6
    @8
    cmul
    co
    #
    @6
    @7
    cdiv
    co
    #
    @5
    @11
    cfv
    @19
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
    @22
    @23
    wceq
    #
    @4
    @1
    @18
    @24
    @13
    cA
    cc
    @5
    cF
    ffvelrn
    sylan
    @4
    @3
    @18
    @27
    @15
    @3
    @18
    wa
    @7
    @2
    wcel
    @27
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
    @24
    @25
    @26
    @28
    @24
    @25
    @26
    w3a
    @23
    @22
    @6
    @7
    divrec
    eqcomd
    3expb
    syl2anc
    @4
    cA
    cA
    @6
    @7
    cdiv
    cA
    cF
    cG
    cV
    cV
    @5
    @14
    @16
    @12
    @12
    @17
    @20
    @21
    ofval
    eqtr4d
    offveq
end
