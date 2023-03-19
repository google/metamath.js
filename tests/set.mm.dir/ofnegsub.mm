include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cmin.mm"
include "simp1.mm"
include "wfn.mm"
include "simp2.mm"
include "ffn.mm"
include "syl.mm"
include "ax-1cn.mm"
include "negcli.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "simp3.mm"
include "inidm.mm"
include "offn.mm"
include "wa.mm"
include "eqidd.mm"
include "a1i.mm"
include "ofc1.mm"
include "ffvelrnda.mm"
include "mulm1d.mm"
include "eqtrd.mm"
include "negsubd.mm"
include "ofval.mm"
include "eqtr4d.mm"
include "offveq.mm"

theorem ofnegsub
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ F : A --> CC /\ G : A --> CC ) -> ( F oF + ( ( A X. { -u 1 } ) oF x. G ) ) = ( F oF - G ) )

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
    cA
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
    cneg
    #
    caddc
    cF
    cA
    c1
    cneg
    #
    csn
    cxp
    #
    cG
    cmul
    cof
    co
    #
    cF
    cG
    cmin
    cof
    co
    #
    cV
    @0
    @1
    @2
    simp1
    #
    @3
    @1
    cF
    cA
    wfn
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
    cA
    cA
    cmul
    cA
    @9
    cG
    cV
    cV
    @8
    cc
    wcel
    #
    @9
    cA
    wfn
    @3
    c1
    ax-1cn
    negcli
    #
    cA
    @8
    cc
    fnconstg
    mp1i
    @3
    @2
    cG
    cA
    wfn
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
    @12
    @12
    cA
    inidm
    #
    offn
    @3
    cA
    cA
    cmin
    cA
    cF
    cG
    cV
    cV
    @14
    @18
    @12
    @12
    @19
    offn
    @3
    @4
    cA
    wcel
    wa
    #
    @5
    eqidd
    #
    @20
    @4
    @10
    cfv
    @8
    @6
    cmul
    co
    @7
    @3
    cA
    @8
    @6
    cmul
    cG
    cV
    cc
    @4
    @12
    @15
    @3
    @16
    a1i
    @18
    @20
    @6
    eqidd
    #
    ofc1
    @20
    @6
    @3
    cA
    cc
    @4
    cG
    @17
    ffvelrnda
    #
    mulm1d
    eqtrd
    @20
    @5
    @7
    caddc
    co
    @5
    @6
    cmin
    co
    @4
    @11
    cfv
    @20
    @5
    @6
    @3
    cA
    cc
    @4
    cF
    @13
    ffvelrnda
    @23
    negsubd
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
    @14
    @18
    @12
    @12
    @19
    @21
    @22
    ofval
    eqtr4d
    offveq
end
