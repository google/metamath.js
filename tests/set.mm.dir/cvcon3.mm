include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "cort.mm"
include "cfv.mm"
include "ccv.mm"
include "wbr.mm"
include "chpsscon3.mm"
include "wb.mm"
include "adantlr.mm"
include "ancoms.mm"
include "adantll.mm"
include "anbi12d.mm"
include "wi.mm"
include "choccl.mm"
include "wceq.mm"
include "psseq2.mm"
include "psseq1.mm"
include "rspcev.mm"
include "sylan.mm"
include "ex.mm"
include "ancomsd.mm"
include "adantl.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "chpsscon1.mm"
include "chpsscon2.mm"
include "impbid.mm"
include "notbid.mm"
include "cvbr.mm"
include "syl2anr.mm"
include "3bitr4d.mm"

theorem cvcon3
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A <oH B <-> ( _|_ ` B ) <oH ( _|_ ` A ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cB
    wpss
    #
    cA
    vx
    cv
    #
    wpss
    #
    @4
    cB
    wpss
    #
    wa
    #
    vx
    cch
    wrex
    #
    wn
    #
    wa
    cB
    cort
    cfv
    #
    cA
    cort
    cfv
    #
    wpss
    #
    @10
    vy
    cv
    #
    wpss
    #
    @13
    @11
    wpss
    #
    wa
    #
    vy
    cch
    wrex
    #
    wn
    #
    wa
    #
    cA
    cB
    ccv
    wbr
    @10
    @11
    ccv
    wbr
    #
    @2
    @3
    @12
    @9
    @18
    cA
    cB
    chpsscon3
    @2
    @8
    @17
    @2
    @8
    @17
    @2
    @7
    @17
    vx
    cch
    @2
    @4
    cch
    wcel
    #
    wa
    #
    @7
    @4
    cort
    cfv
    #
    @11
    wpss
    #
    @10
    @23
    wpss
    #
    wa
    #
    @17
    @22
    @5
    @24
    @6
    @25
    @0
    @21
    @5
    @24
    wb
    @1
    cA
    @4
    chpsscon3
    adantlr
    @1
    @21
    @6
    @25
    wb
    #
    @0
    @21
    @1
    @27
    @4
    cB
    chpsscon3
    ancoms
    adantll
    anbi12d
    @21
    @26
    @17
    wi
    @2
    @21
    @25
    @24
    @17
    @21
    @25
    @24
    wa
    #
    @17
    @21
    @23
    cch
    wcel
    @28
    @17
    @4
    choccl
    @16
    @28
    vy
    @23
    cch
    @13
    @23
    wceq
    @14
    @25
    @15
    @24
    @13
    @23
    @10
    psseq2
    @13
    @23
    @11
    psseq1
    anbi12d
    rspcev
    sylan
    ex
    ancomsd
    adantl
    sylbid
    rexlimdva
    @2
    @16
    @8
    vy
    cch
    @2
    @13
    cch
    wcel
    #
    wa
    #
    @16
    @13
    cort
    cfv
    #
    cB
    wpss
    #
    cA
    @31
    wpss
    #
    wa
    #
    @8
    @30
    @14
    @32
    @15
    @33
    @1
    @29
    @14
    @32
    wb
    @0
    cB
    @13
    chpsscon1
    adantll
    @0
    @29
    @15
    @33
    wb
    #
    @1
    @29
    @0
    @35
    @13
    cA
    chpsscon2
    ancoms
    adantlr
    anbi12d
    @29
    @34
    @8
    wi
    @2
    @29
    @33
    @32
    @8
    @29
    @33
    @32
    wa
    #
    @8
    @29
    @31
    cch
    wcel
    @36
    @8
    @13
    choccl
    @7
    @36
    vx
    @31
    cch
    @4
    @31
    wceq
    @5
    @33
    @6
    @32
    @4
    @31
    cA
    psseq2
    @4
    @31
    cB
    psseq1
    anbi12d
    rspcev
    sylan
    ex
    ancomsd
    adantl
    sylbid
    rexlimdva
    impbid
    notbid
    anbi12d
    vx
    cA
    cB
    cvbr
    @1
    @10
    cch
    wcel
    @11
    cch
    wcel
    @20
    @19
    wb
    @0
    cB
    choccl
    cA
    choccl
    vy
    @10
    @11
    cvbr
    syl2anr
    3bitr4d
end
