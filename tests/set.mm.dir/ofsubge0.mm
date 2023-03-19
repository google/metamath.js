include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "w3a.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cofr.mm"
include "wa.mm"
include "simp2.mm"
include "ffvelrnda.mm"
include "simp3.mm"
include "subge0d.mm"
include "ralbidva.mm"
include "cc.mm"
include "wfn.mm"
include "0cn.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "ffn.mm"
include "syl.mm"
include "simp1.mm"
include "inidm.mm"
include "offn.mm"
include "wceq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "eqidd.mm"
include "ofval.mm"
include "ofrfval.mm"
include "3bitr4d.mm"

theorem ofsubge0
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ F : A --> RR /\ G : A --> RR ) -> ( ( A X. { 0 } ) oR <_ ( F oF - G ) <-> G oR <_ F ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cr
    cF
    wf
    #
    cA
    cr
    cG
    wf
    #
    w3a
    #
    cc0
    vx
    cv
    #
    cF
    cfv
    #
    @4
    cG
    cfv
    #
    cmin
    co
    #
    cle
    wbr
    #
    vx
    cA
    wral
    @6
    @5
    cle
    wbr
    #
    vx
    cA
    wral
    cA
    cc0
    csn
    cxp
    #
    cF
    cG
    cmin
    cof
    co
    #
    cle
    cofr
    #
    wbr
    cG
    cF
    @12
    wbr
    @3
    @8
    @9
    vx
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @5
    @6
    @3
    cA
    cr
    @4
    cF
    @0
    @1
    @2
    simp2
    #
    ffvelrnda
    @3
    cA
    cr
    @4
    cG
    @0
    @1
    @2
    simp3
    #
    ffvelrnda
    subge0d
    ralbidva
    @3
    vx
    cA
    cA
    cc0
    @7
    cle
    cA
    @10
    @11
    cV
    cV
    cc0
    cc
    wcel
    @10
    cA
    wfn
    @3
    0cn
    cA
    cc0
    cc
    fnconstg
    mp1i
    @3
    cA
    cA
    cmin
    cA
    cF
    cG
    cV
    cV
    @3
    @1
    cF
    cA
    wfn
    @15
    cA
    cr
    cF
    ffn
    syl
    #
    @3
    @2
    cG
    cA
    wfn
    @16
    cA
    cr
    cG
    ffn
    syl
    #
    @0
    @1
    @2
    simp1
    #
    @19
    cA
    inidm
    #
    offn
    @19
    @19
    @20
    @13
    @4
    @10
    cfv
    cc0
    wceq
    @3
    cA
    cc0
    @4
    c0ex
    fvconst2
    adantl
    @3
    cA
    cA
    @5
    @6
    cmin
    cA
    cF
    cG
    cV
    cV
    @4
    @17
    @18
    @19
    @19
    @20
    @14
    @5
    eqidd
    #
    @14
    @6
    eqidd
    #
    ofval
    ofrfval
    @3
    vx
    cA
    cA
    @6
    @5
    cle
    cA
    cG
    cF
    cV
    cV
    @18
    @17
    @19
    @19
    @20
    @22
    @21
    ofrfval
    3bitr4d
end
