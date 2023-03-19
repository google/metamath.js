include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "psmettri2.mm"
include "syl13anc.mm"
include "cc0.mm"
include "psmet0.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "cxr.mm"
include "psmetcl.mm"
include "xaddid1.mm"
include "syl.mm"
include "3com23.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "3adant3.mm"
include "wa.mm"
include "wb.mm"
include "xrletri3.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem psmetsym
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cC: class C


  assert |- ( ( D e. ( PsMet ` X ) /\ A e. X /\ B e. X ) -> ( A D B ) = ( B D A ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cD
    co
    #
    cB
    cA
    cD
    co
    #
    wceq
    #
    @4
    @5
    cle
    wbr
    #
    @5
    @4
    cle
    wbr
    #
    @3
    @4
    @5
    cB
    cB
    cD
    co
    #
    cxad
    co
    #
    @5
    cle
    @3
    @0
    @2
    @1
    @2
    @4
    @10
    cle
    wbr
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp2
    #
    @12
    cA
    cB
    cB
    cD
    cX
    psmettri2
    syl13anc
    @3
    @10
    @5
    cc0
    cxad
    co
    #
    @5
    @3
    @9
    cc0
    @5
    cxad
    @0
    @2
    @9
    cc0
    wceq
    @1
    cB
    cD
    cX
    psmet0
    3adant2
    oveq2d
    @0
    @2
    @1
    @14
    @5
    wceq
    #
    @0
    @2
    @1
    w3a
    @5
    cxr
    wcel
    #
    @15
    cB
    cA
    cD
    cX
    psmetcl
    #
    @5
    xaddid1
    syl
    3com23
    eqtrd
    breqtrd
    @3
    @5
    @4
    cA
    cA
    cD
    co
    #
    cxad
    co
    #
    @4
    cle
    @3
    @0
    @1
    @2
    @1
    @5
    @19
    cle
    wbr
    @11
    @13
    @12
    @13
    cB
    cA
    cA
    cD
    cX
    psmettri2
    syl13anc
    @3
    @19
    @4
    cc0
    cxad
    co
    #
    @4
    @3
    @18
    cc0
    @4
    cxad
    @0
    @1
    @18
    cc0
    wceq
    @2
    cA
    cD
    cX
    psmet0
    3adant3
    oveq2d
    @3
    @4
    cxr
    wcel
    #
    @20
    @4
    wceq
    cA
    cB
    cD
    cX
    psmetcl
    #
    @4
    xaddid1
    syl
    eqtrd
    breqtrd
    @3
    @21
    @16
    @6
    @7
    @8
    wa
    wb
    @22
    @0
    @2
    @1
    @16
    @17
    3com23
    @4
    @5
    xrletri3
    syl2anc
    mpbir2and
end
