include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "crp.mm"
include "cc.mm"
include "w3a.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "ccxp.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2.mm"
include "rpreccld.mm"
include "rpred.mm"
include "rpge0d.mm"
include "simp3.mm"
include "mulcxp.mm"
include "syl221anc.mm"
include "cxprec.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "recnd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "oveq1d.mm"
include "cxpcl.mm"
include "wne.mm"
include "cxpne0.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"

theorem divcxp
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ B e. RR+ /\ C e. CC ) -> ( ( A / B ) ^c C ) = ( ( A ^c C ) / ( B ^c C ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    cB
    crp
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cC
    ccxp
    co
    #
    cA
    cC
    ccxp
    co
    #
    c1
    cB
    cC
    ccxp
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    cA
    cB
    cdiv
    co
    #
    cC
    ccxp
    co
    @9
    @10
    cdiv
    co
    @5
    @8
    @9
    @6
    cC
    ccxp
    co
    #
    cmul
    co
    #
    @12
    @5
    @0
    @1
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    @4
    @8
    @15
    wceq
    @0
    @1
    @3
    @4
    simp1l
    #
    @0
    @1
    @3
    @4
    simp1r
    @5
    @6
    @5
    cB
    @2
    @3
    @4
    simp2
    #
    rpreccld
    #
    rpred
    @5
    @6
    @18
    rpge0d
    @2
    @3
    @4
    simp3
    #
    cA
    @6
    cC
    mulcxp
    syl221anc
    @5
    @14
    @11
    @9
    cmul
    @5
    @3
    @4
    @14
    @11
    wceq
    @17
    @19
    cB
    cC
    cxprec
    syl2anc
    oveq2d
    eqtrd
    @5
    @13
    @7
    cC
    ccxp
    @5
    cA
    cB
    @5
    cA
    @16
    recnd
    #
    @5
    cB
    @17
    rpcnd
    #
    @5
    cB
    @17
    rpne0d
    #
    divrecd
    oveq1d
    @5
    @9
    @10
    @5
    cA
    cc
    wcel
    @4
    @9
    cc
    wcel
    @20
    @19
    cA
    cC
    cxpcl
    syl2anc
    @5
    cB
    cc
    wcel
    #
    @4
    @10
    cc
    wcel
    @21
    @19
    cB
    cC
    cxpcl
    syl2anc
    @5
    @23
    cB
    cc0
    wne
    @4
    @10
    cc0
    wne
    @21
    @22
    @19
    cB
    cC
    cxpne0
    syl3anc
    divrecd
    3eqtr4d
end
