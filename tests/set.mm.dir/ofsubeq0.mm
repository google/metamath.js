include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wfn.mm"
include "simp2.mm"
include "ffn.mm"
include "syl.mm"
include "simp3.mm"
include "simp1.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "ffvelrnda.mm"
include "subeq0ad.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "wb.mm"
include "offn.mm"
include "fconst.mm"
include "ax-mp.mm"
include "eqfnfv.mm"
include "sylancl.mm"
include "syl2anc.mm"
include "3bitr4d.mm"

theorem ofsubeq0
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ F : A --> CC /\ G : A --> CC ) -> ( ( F oF - G ) = ( A X. { 0 } ) <-> F = G ) )

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
    cv
    #
    cF
    cG
    cmin
    cof
    co
    #
    cfv
    #
    @4
    cA
    cc0
    csn
    #
    cxp
    #
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @4
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @5
    @8
    wceq
    #
    cF
    cG
    wceq
    #
    @3
    @10
    @14
    vx
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @10
    @12
    @13
    cmin
    co
    #
    cc0
    wceq
    @14
    @19
    @6
    @20
    @9
    cc0
    @3
    cA
    cA
    @12
    @13
    cmin
    cA
    cF
    cG
    cV
    cV
    @4
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
    @27
    cA
    inidm
    #
    @19
    @12
    eqidd
    @19
    @13
    eqidd
    ofval
    @18
    @9
    cc0
    wceq
    @3
    cA
    cc0
    @4
    c0ex
    fvconst2
    adantl
    eqeq12d
    @19
    @12
    @13
    @3
    cA
    cc
    @4
    cF
    @22
    ffvelrnda
    @3
    cA
    cc
    @4
    cG
    @25
    ffvelrnda
    subeq0ad
    bitrd
    ralbidva
    @3
    @5
    cA
    wfn
    @8
    cA
    wfn
    #
    @16
    @11
    wb
    @3
    cA
    cA
    cmin
    cA
    cF
    cG
    cV
    cV
    @23
    @26
    @27
    @27
    @28
    offn
    cA
    @7
    @8
    wf
    @29
    cA
    cc0
    c0ex
    fconst
    cA
    @7
    @8
    ffn
    ax-mp
    vx
    cA
    @5
    @8
    eqfnfv
    sylancl
    @3
    @21
    @24
    @17
    @15
    wb
    @23
    @26
    vx
    cA
    cF
    cG
    eqfnfv
    syl2anc
    3bitr4d
end
