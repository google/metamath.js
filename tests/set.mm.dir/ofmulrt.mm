include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "w3a.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccnv.mm"
include "cc0.mm"
include "csn.mm"
include "cima.mm"
include "cun.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "wfn.mm"
include "simp2.mm"
include "ffn.mm"
include "syl.mm"
include "simp3.mm"
include "simp1.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "eqeq1d.mm"
include "ffvelrnda.mm"
include "mul0ord.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "wb.mm"
include "offn.mm"
include "fniniseg.mm"
include "orbi12d.mm"
include "elun.mm"
include "andi.mm"
include "3bitr4g.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem ofmulrt
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let cS: class S


  assert |- ( ( A e. V /\ F : A --> CC /\ G : A --> CC ) -> ( `' ( F oF x. G ) " { 0 } ) = ( ( `' F " { 0 } ) u. ( `' G " { 0 } ) ) )

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
    cG
    wf
    #
    w3a
    #
    vx
    cF
    cG
    cmul
    cof
    co
    #
    ccnv
    cc0
    csn
    #
    cima
    #
    cF
    ccnv
    @5
    cima
    #
    cG
    ccnv
    @5
    cima
    #
    cun
    #
    @3
    vx
    cv
    #
    cA
    wcel
    #
    @10
    @4
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @11
    @10
    cF
    cfv
    #
    cc0
    wceq
    #
    @10
    cG
    cfv
    #
    cc0
    wceq
    #
    wo
    #
    wa
    #
    @10
    @6
    wcel
    #
    @10
    @9
    wcel
    #
    @3
    @11
    @13
    @19
    @3
    @11
    wa
    #
    @13
    @15
    @17
    cmul
    co
    #
    cc0
    wceq
    @19
    @23
    @12
    @24
    cc0
    @3
    cA
    cA
    @15
    @17
    cmul
    cA
    cF
    cG
    cV
    cV
    @10
    @3
    @1
    cF
    cA
    wfn
    #
    @0
    @1
    @2
    simp2
    #
    cA
    cc
    cF
    ffn
    syl
    #
    @3
    @2
    cG
    cA
    wfn
    #
    @0
    @1
    @2
    simp3
    #
    cA
    cc
    cG
    ffn
    syl
    #
    @0
    @1
    @2
    simp1
    #
    @31
    cA
    inidm
    #
    @23
    @15
    eqidd
    @23
    @17
    eqidd
    ofval
    eqeq1d
    @23
    @15
    @17
    @3
    cA
    cc
    @10
    cF
    @26
    ffvelrnda
    @3
    cA
    cc
    @10
    cG
    @29
    ffvelrnda
    mul0ord
    bitrd
    pm5.32da
    @3
    @4
    cA
    wfn
    @21
    @14
    wb
    @3
    cA
    cA
    cmul
    cA
    cF
    cG
    cV
    cV
    @27
    @30
    @31
    @31
    @32
    offn
    cA
    cc0
    @10
    @4
    fniniseg
    syl
    @3
    @10
    @7
    wcel
    #
    @10
    @8
    wcel
    #
    wo
    @11
    @16
    wa
    #
    @11
    @18
    wa
    #
    wo
    @22
    @20
    @3
    @33
    @35
    @34
    @36
    @3
    @25
    @33
    @35
    wb
    @27
    cA
    cc0
    @10
    cF
    fniniseg
    syl
    @3
    @28
    @34
    @36
    wb
    @30
    cA
    cc0
    @10
    cG
    fniniseg
    syl
    orbi12d
    @10
    @7
    @8
    elun
    @11
    @16
    @18
    andi
    3bitr4g
    3bitr4d
    eqrdv
end
