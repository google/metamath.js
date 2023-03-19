include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wrex.mm"
include "wa.mm"
include "cfn.mm"
include "peano2.mm"
include "breq2.mm"
include "rspcev.mm"
include "isfi.mm"
include "sylibr.mm"
include "sylan.mm"
include "diffi.mm"
include "sylib.mm"
include "syl.mm"
include "3adant3.mm"
include "wceq.mm"
include "cun.mm"
include "wi.mm"
include "cin.mm"
include "c0.mm"
include "cvv.mm"
include "vex.mm"
include "en2sn.mm"
include "mpan2.mm"
include "word.mm"
include "nnord.mm"
include "orddisj.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "unen.mm"
include "an4s.mm"
include "mpanl2.mm"
include "expcom.mm"
include "syl2an.mm"
include "3ad2antl3.mm"
include "wb.mm"
include "difsnid.mm"
include "df-suc.mm"
include "eqcomi.mm"
include "a1i.mm"
include "breq12d.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "ensym.mm"
include "entr.mm"
include "nneneq.mm"
include "sylan2.mm"
include "syl5ib.mm"
include "expd.mm"
include "syl5.mm"
include "imp.mm"
include "an32s.mm"
include "3adantl3.mm"
include "sylbid.mm"
include "peano4.mm"
include "biimpd.mm"
include "3ad2antl1.mm"
include "3syld.mm"
include "biimprcd.mm"
include "sylcom.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem dif1en
  let cA: class A
  let cM: class M
  let cX: class X
  let vx: setvar x


  assert |- ( ( M e. _om /\ A ~~ suc M /\ X e. A ) -> ( A \ { X } ) ~~ M )

  proof
    cM
    com
    wcel
    #
    cA
    cM
    csuc
    #
    cen
    wbr
    #
    cX
    cA
    wcel
    #
    w3a
    #
    cA
    cX
    csn
    #
    cdif
    #
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    #
    @6
    cM
    cen
    wbr
    #
    @0
    @2
    @9
    @3
    @0
    @2
    wa
    cA
    cfn
    wcel
    #
    @9
    @0
    @1
    com
    wcel
    #
    @2
    @11
    cM
    peano2
    #
    @12
    @2
    wa
    cA
    @7
    cen
    wbr
    #
    vx
    com
    wrex
    @11
    @14
    @2
    vx
    @1
    com
    @7
    @1
    cA
    cen
    breq2
    rspcev
    vx
    cA
    isfi
    sylibr
    sylan
    @11
    @6
    cfn
    wcel
    @9
    cA
    @5
    diffi
    vx
    @6
    isfi
    sylib
    syl
    3adant3
    @4
    @8
    @10
    vx
    com
    @4
    @7
    com
    wcel
    #
    wa
    #
    @8
    cM
    @7
    wceq
    #
    @10
    @16
    @8
    @6
    @5
    cun
    #
    @7
    @7
    csn
    #
    cun
    #
    cen
    wbr
    #
    @1
    @7
    csuc
    #
    wceq
    #
    @17
    @3
    @0
    @15
    @8
    @21
    wi
    #
    @2
    @3
    @5
    @19
    cen
    wbr
    #
    @7
    @19
    cin
    c0
    wceq
    #
    @24
    @15
    @3
    @7
    cvv
    wcel
    @25
    vx
    vex
    cX
    @7
    cA
    cvv
    en2sn
    mpan2
    @15
    @7
    word
    @26
    @7
    nnord
    @7
    orddisj
    syl
    @8
    @25
    @26
    wa
    #
    @21
    @8
    @6
    @5
    cin
    #
    c0
    wceq
    #
    @27
    @21
    @28
    @5
    @6
    cin
    c0
    @6
    @5
    incom
    @5
    cA
    disjdif
    eqtri
    @8
    @25
    @29
    @26
    @21
    @6
    @7
    @5
    @19
    unen
    an4s
    mpanl2
    expcom
    syl2an
    3ad2antl3
    @16
    @21
    cA
    @22
    cen
    wbr
    #
    @23
    @4
    @21
    @30
    wb
    #
    @15
    @3
    @0
    @31
    @2
    @3
    @18
    cA
    @20
    @22
    cen
    cA
    cX
    difsnid
    @20
    @22
    wceq
    @3
    @22
    @20
    @7
    df-suc
    eqcomi
    a1i
    breq12d
    3ad2ant3
    adantr
    @0
    @2
    @15
    @30
    @23
    wi
    #
    @3
    @0
    @15
    @2
    @32
    @0
    @15
    wa
    #
    @2
    @32
    @0
    @12
    @15
    @2
    @32
    wi
    @13
    @2
    @1
    cA
    cen
    wbr
    #
    @12
    @15
    wa
    #
    @32
    cA
    @1
    ensym
    @35
    @34
    @30
    @23
    @34
    @30
    wa
    @1
    @22
    cen
    wbr
    #
    @35
    @23
    @1
    cA
    @22
    entr
    @15
    @12
    @22
    com
    wcel
    @36
    @23
    wb
    @7
    peano2
    @1
    @22
    nneneq
    sylan2
    syl5ib
    expd
    syl5
    sylan
    imp
    an32s
    3adantl3
    sylbid
    @0
    @2
    @15
    @23
    @17
    wi
    @3
    @33
    @23
    @17
    cM
    @7
    peano4
    biimpd
    3ad2antl1
    3syld
    @17
    @10
    @8
    cM
    @7
    @6
    cen
    breq2
    biimprcd
    sylcom
    rexlimdva
    mpd
end
