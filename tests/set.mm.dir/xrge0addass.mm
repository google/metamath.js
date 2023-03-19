include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "cxad.mm"
include "wceq.mm"
include "iccssxr.mm"
include "simp1.mm"
include "sseldi.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "elicc4.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "ge0nemnf.mm"
include "syl2anc.mm"
include "simp2.mm"
include "simp3.mm"
include "xaddass.mm"
include "syl222anc.mm"

theorem xrge0addass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\ C e. ( 0 [,] +oo ) ) -> ( ( A +e B ) +e C ) = ( A +e ( B +e C ) ) )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    #
    cA
    cxr
    wcel
    #
    cA
    cmnf
    wne
    #
    cB
    cxr
    wcel
    #
    cB
    cmnf
    wne
    #
    cC
    cxr
    wcel
    #
    cC
    cmnf
    wne
    #
    cA
    cB
    cxad
    co
    cC
    cxad
    co
    cA
    cB
    cC
    cxad
    co
    cxad
    co
    wceq
    @4
    @0
    cxr
    cA
    cc0
    cpnf
    iccssxr
    #
    @1
    @2
    @3
    simp1
    #
    sseldi
    #
    @4
    @5
    cc0
    cA
    cle
    wbr
    #
    @6
    @13
    @4
    @14
    cA
    cpnf
    cle
    wbr
    #
    @4
    @1
    @14
    @15
    wa
    #
    @12
    @4
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @5
    @1
    @16
    wb
    @17
    @4
    0xr
    a1i
    #
    @18
    @4
    pnfxr
    a1i
    #
    @13
    cc0
    cpnf
    cA
    elicc4
    syl3anc
    mpbid
    simpld
    cA
    ge0nemnf
    syl2anc
    @4
    @0
    cxr
    cB
    @11
    @1
    @2
    @3
    simp2
    #
    sseldi
    #
    @4
    @7
    cc0
    cB
    cle
    wbr
    #
    @8
    @22
    @4
    @23
    cB
    cpnf
    cle
    wbr
    #
    @4
    @2
    @23
    @24
    wa
    #
    @21
    @4
    @17
    @18
    @7
    @2
    @25
    wb
    @19
    @20
    @22
    cc0
    cpnf
    cB
    elicc4
    syl3anc
    mpbid
    simpld
    cB
    ge0nemnf
    syl2anc
    @4
    @0
    cxr
    cC
    @11
    @1
    @2
    @3
    simp3
    #
    sseldi
    #
    @4
    @9
    cc0
    cC
    cle
    wbr
    #
    @10
    @27
    @4
    @28
    cC
    cpnf
    cle
    wbr
    #
    @4
    @3
    @28
    @29
    wa
    #
    @26
    @4
    @17
    @18
    @9
    @3
    @30
    wb
    @19
    @20
    @27
    cc0
    cpnf
    cC
    elicc4
    syl3anc
    mpbid
    simpld
    cC
    ge0nemnf
    syl2anc
    cA
    cB
    cC
    xaddass
    syl222anc
end
