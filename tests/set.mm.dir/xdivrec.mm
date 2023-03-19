include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cxdiv.mm"
include "co.mm"
include "c1.mm"
include "cxmu.mm"
include "wceq.mm"
include "simp2.mm"
include "rexrd.mm"
include "simp1.mm"
include "1re.mm"
include "rexri.mm"
include "a1i.mm"
include "simp3.mm"
include "xdivcld.mm"
include "xmulcld.mm"
include "xmulcom.mm"
include "syl2anc.mm"
include "xmulass.mm"
include "syl3anc.mm"
include "eqid.mm"
include "wb.mm"
include "xdivmul.mm"
include "syl112anc.mm"
include "mpbii.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "xmulid1.mm"
include "syl.mm"
include "mpbird.mm"

theorem xdivrec
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR /\ B =/= 0 ) -> ( A /e B ) = ( A *e ( 1 /e B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cB
    cxdiv
    co
    cA
    c1
    cB
    cxdiv
    co
    #
    cxmu
    co
    #
    wceq
    #
    cB
    @5
    cxmu
    co
    #
    cA
    wceq
    #
    @3
    @7
    cA
    c1
    cxmu
    co
    #
    cA
    @3
    @7
    @5
    cB
    cxmu
    co
    #
    cA
    @4
    cB
    cxmu
    co
    #
    cxmu
    co
    #
    @9
    @3
    cB
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @7
    @10
    wceq
    @3
    cB
    @0
    @1
    @2
    simp2
    #
    rexrd
    #
    @3
    cA
    @4
    @0
    @1
    @2
    simp1
    #
    @3
    c1
    cB
    c1
    cxr
    wcel
    #
    @3
    c1
    1re
    rexri
    a1i
    #
    @15
    @0
    @1
    @2
    simp3
    #
    xdivcld
    #
    xmulcld
    #
    cB
    @5
    xmulcom
    syl2anc
    @3
    @0
    @4
    cxr
    wcel
    #
    @13
    @10
    @12
    wceq
    @17
    @21
    @16
    cA
    @4
    cB
    xmulass
    syl3anc
    @3
    @11
    c1
    cA
    cxmu
    @3
    @11
    cB
    @4
    cxmu
    co
    #
    c1
    @3
    @23
    @13
    @11
    @24
    wceq
    @21
    @16
    @4
    cB
    xmulcom
    syl2anc
    @3
    @4
    @4
    wceq
    #
    @24
    c1
    wceq
    #
    @4
    eqid
    @3
    @18
    @23
    @1
    @2
    @25
    @26
    wb
    @19
    @21
    @15
    @20
    c1
    @4
    cB
    xdivmul
    syl112anc
    mpbii
    eqtrd
    oveq2d
    3eqtrd
    @3
    @0
    @9
    cA
    wceq
    @17
    cA
    xmulid1
    syl
    eqtrd
    @3
    @0
    @14
    @1
    @2
    @6
    @8
    wb
    @17
    @22
    @15
    @20
    cA
    @5
    cB
    xdivmul
    syl112anc
    mpbird
end
