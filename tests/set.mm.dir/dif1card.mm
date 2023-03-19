include "cfn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "csuc.mm"
include "wceq.mm"
include "wi.mm"
include "diffi.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wrex.mm"
include "isfi.mm"
include "wa.mm"
include "w3a.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "simp3.mm"
include "en2sn.mm"
include "3adant3.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "wel.mm"
include "wn.mm"
include "word.mm"
include "nnord.mm"
include "ordirr.mm"
include "syl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "3ad2ant2.mm"
include "unen.mm"
include "syl22anc.mm"
include "wb.mm"
include "difsnid.mm"
include "df-suc.mm"
include "eqcomi.mm"
include "breq12d.mm"
include "3ad2ant1.mm"
include "mpbid.mm"
include "peano2.mm"
include "cardennn.mm"
include "syl2anc.mm"
include "ancoms.mm"
include "3adant1.mm"
include "suceq.mm"
include "eqtr4d.mm"
include "3expib.mm"
include "com12.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "imp.mm"

theorem dif1card
  let cA: class A
  let cX: class X
  let vm: setvar m


  assert |- ( ( A e. Fin /\ X e. A ) -> ( card ` A ) = suc ( card ` ( A \ { X } ) ) )

  proof
    cA
    cfn
    wcel
    #
    cX
    cA
    wcel
    #
    cA
    ccrd
    cfv
    #
    cA
    cX
    csn
    #
    cdif
    #
    ccrd
    cfv
    #
    csuc
    #
    wceq
    #
    @0
    @4
    cfn
    wcel
    #
    @1
    @7
    wi
    #
    cA
    @3
    diffi
    @8
    @4
    vm
    cv
    #
    cen
    wbr
    #
    vm
    com
    wrex
    @9
    vm
    @4
    isfi
    @11
    @9
    vm
    com
    @1
    @10
    com
    wcel
    #
    @11
    wa
    @7
    @1
    @12
    @11
    @7
    @1
    @12
    @11
    w3a
    #
    @2
    @10
    csuc
    #
    @6
    @13
    cA
    @14
    cen
    wbr
    #
    @14
    com
    wcel
    #
    @2
    @14
    wceq
    @13
    @4
    @3
    cun
    #
    @10
    @10
    csn
    #
    cun
    #
    cen
    wbr
    #
    @15
    @13
    @11
    @3
    @18
    cen
    wbr
    #
    @4
    @3
    cin
    #
    c0
    wceq
    #
    @10
    @18
    cin
    c0
    wceq
    #
    @20
    @1
    @12
    @11
    simp3
    @1
    @12
    @21
    @11
    cX
    @10
    cA
    com
    en2sn
    3adant3
    @23
    @13
    @22
    @3
    @4
    cin
    c0
    @4
    @3
    incom
    @3
    cA
    disjdif
    eqtri
    a1i
    @12
    @1
    @24
    @11
    @12
    vm
    vm
    wel
    wn
    #
    @24
    @12
    @10
    word
    @25
    @10
    nnord
    @10
    ordirr
    syl
    @10
    @10
    disjsn
    sylibr
    3ad2ant2
    @4
    @10
    @3
    @18
    unen
    syl22anc
    @1
    @12
    @20
    @15
    wb
    @11
    @1
    @17
    cA
    @19
    @14
    cen
    cA
    cX
    difsnid
    @19
    @14
    wceq
    @1
    @14
    @19
    @10
    df-suc
    eqcomi
    a1i
    breq12d
    3ad2ant1
    mpbid
    @12
    @1
    @16
    @11
    @10
    peano2
    3ad2ant2
    cA
    @14
    cardennn
    syl2anc
    @13
    @5
    @10
    wceq
    #
    @6
    @14
    wceq
    @12
    @11
    @26
    @1
    @11
    @12
    @26
    @4
    @10
    cardennn
    ancoms
    3adant1
    @5
    @10
    suceq
    syl
    eqtr4d
    3expib
    com12
    rexlimiva
    sylbi
    syl
    imp
end
