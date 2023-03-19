include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cbs.mm"
include "cple.mm"
include "wbr.mm"
include "wb.mm"
include "wi.mm"
include "ccnv.mm"
include "wf1o.mm"
include "simpl1.mm"
include "simpl3.mm"
include "eqid.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "simpr3.mm"
include "ltrncnvat.mm"
include "syl3anc.mm"
include "atbase.mm"
include "syl.mm"
include "f1ocnvfv1.mm"
include "simpr2.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "f1ocnvfv2.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "simpr1.mm"
include "breq2d.mm"
include "3bitr4d.mm"
include "claut.mm"
include "simpl1l.mm"
include "ltrnlaut.mm"
include "ltrncl.mm"
include "lautcnvle.mm"
include "syl22anc.mm"
include "3exp2.mm"
include "imp.mm"
include "ralrimdv.mm"
include "simpr.mm"
include "hlateq.mm"
include "sylibd.mm"
include "ralrimdva.mm"
include "wfn.mm"
include "3adant3.mm"
include "f1ofn.mm"
include "3adant2.mm"
include "eqfnfv.mm"
include "sylibrd.mm"
include "fveq1.mm"
include "ralrimivw.mm"
include "impbid1.mm"

theorem ltrneq2
  let cA: class A
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  assume ltrneq2.a: |- A = ( Atoms ` K )
  assume ltrneq2.h: |- H = ( LHyp ` K )
  assume ltrneq2.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint A p
  disjoint F p
  disjoint G p
  disjoint p q
  disjoint p x
  disjoint q x
  disjoint A q
  disjoint A x
  disjoint F q
  disjoint F x
  disjoint G q
  disjoint G x
  disjoint H q
  disjoint H x
  disjoint K q
  disjoint K x
  disjoint T q
  disjoint T x
  disjoint W q
  disjoint W x
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( A. p e. A ( F ` p ) = ( G ` p ) <-> F = G ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
    #
    vp
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    wceq
    #
    vp
    cA
    wral
    #
    cF
    cG
    wceq
    #
    @5
    @10
    vx
    cv
    #
    cF
    cfv
    #
    @12
    cG
    cfv
    #
    wceq
    #
    vx
    cK
    cbs
    cfv
    #
    wral
    #
    @11
    @5
    @10
    @15
    vx
    @16
    @5
    @12
    @16
    wcel
    #
    wa
    #
    @10
    vq
    cv
    #
    @13
    cK
    cple
    cfv
    #
    wbr
    #
    @20
    @14
    @21
    wbr
    #
    wb
    #
    vq
    cA
    wral
    #
    @15
    @19
    @10
    @24
    vq
    cA
    @5
    @18
    @10
    @20
    cA
    wcel
    #
    @24
    wi
    wi
    @5
    @18
    @10
    @26
    @24
    @5
    @18
    @10
    @26
    w3a
    #
    wa
    #
    @20
    cF
    ccnv
    #
    cfv
    #
    @13
    @29
    cfv
    #
    @21
    wbr
    #
    @20
    cG
    ccnv
    #
    cfv
    #
    @14
    @33
    cfv
    #
    @21
    wbr
    #
    @22
    @23
    @28
    @30
    @12
    @21
    wbr
    @34
    @12
    @21
    wbr
    @32
    @36
    @28
    @30
    @34
    @12
    @21
    @28
    @30
    cG
    cfv
    #
    @33
    cfv
    #
    @30
    @34
    @28
    @16
    @16
    cG
    wf1o
    #
    @30
    @16
    wcel
    #
    @38
    @30
    wceq
    @28
    @2
    @4
    @39
    @2
    @3
    @4
    @27
    simpl1
    #
    @2
    @3
    @4
    @27
    simpl3
    #
    @16
    cT
    cG
    cH
    cK
    chlt
    cW
    @16
    eqid
    #
    ltrneq2.h
    ltrneq2.t
    ltrn1o
    #
    syl2anc
    #
    @28
    @30
    cA
    wcel
    #
    @40
    @28
    @2
    @3
    @26
    @46
    @41
    @2
    @3
    @4
    @27
    simpl2
    #
    @5
    @18
    @10
    @26
    simpr3
    #
    cA
    @20
    cT
    cF
    cH
    cK
    @21
    cW
    @21
    eqid
    #
    ltrneq2.a
    ltrneq2.h
    ltrneq2.t
    ltrncnvat
    syl3anc
    #
    cA
    @16
    @30
    cK
    @43
    ltrneq2.a
    atbase
    syl
    @16
    @16
    @30
    cG
    f1ocnvfv1
    syl2anc
    @28
    @37
    @20
    @33
    @28
    @30
    cF
    cfv
    #
    @37
    @20
    @28
    @46
    @10
    @51
    @37
    wceq
    #
    @50
    @5
    @18
    @10
    @26
    simpr2
    @9
    @52
    vp
    @30
    cA
    @6
    @30
    wceq
    @7
    @51
    @8
    @37
    @6
    @30
    cF
    fveq2
    @6
    @30
    cG
    fveq2
    eqeq12d
    rspcv
    sylc
    @28
    @16
    @16
    cF
    wf1o
    #
    @20
    @16
    wcel
    #
    @51
    @20
    wceq
    @28
    @2
    @3
    @53
    @41
    @47
    @16
    cT
    cF
    cH
    cK
    chlt
    cW
    @43
    ltrneq2.h
    ltrneq2.t
    ltrn1o
    #
    syl2anc
    #
    @28
    @26
    @54
    @48
    cA
    @16
    @20
    cK
    @43
    ltrneq2.a
    atbase
    syl
    #
    @16
    @16
    @20
    cF
    f1ocnvfv2
    syl2anc
    eqtr3d
    fveq2d
    eqtr3d
    breq1d
    @28
    @31
    @12
    @30
    @21
    @28
    @53
    @18
    @31
    @12
    wceq
    @56
    @5
    @18
    @10
    @26
    simpr1
    #
    @16
    @16
    @12
    cF
    f1ocnvfv1
    syl2anc
    breq2d
    @28
    @35
    @12
    @34
    @21
    @28
    @39
    @18
    @35
    @12
    wceq
    @45
    @58
    @16
    @16
    @12
    cG
    f1ocnvfv1
    syl2anc
    breq2d
    3bitr4d
    @28
    @0
    cF
    cK
    claut
    cfv
    #
    wcel
    #
    @54
    @13
    @16
    wcel
    #
    @22
    @32
    wb
    @0
    @1
    @3
    @4
    @27
    simpl1l
    #
    @28
    @2
    @3
    @60
    @41
    @47
    cT
    cF
    cH
    @59
    cK
    chlt
    cW
    ltrneq2.h
    @59
    eqid
    #
    ltrneq2.t
    ltrnlaut
    syl2anc
    @57
    @28
    @2
    @3
    @18
    @61
    @41
    @47
    @58
    @16
    cT
    cF
    cH
    cK
    chlt
    cW
    @12
    @43
    ltrneq2.h
    ltrneq2.t
    ltrncl
    #
    syl3anc
    @16
    cF
    @59
    cK
    @21
    chlt
    @20
    @13
    @43
    @49
    @63
    lautcnvle
    syl22anc
    @28
    @0
    cG
    @59
    wcel
    #
    @54
    @14
    @16
    wcel
    #
    @23
    @36
    wb
    @62
    @28
    @2
    @4
    @65
    @41
    @42
    cT
    cG
    cH
    @59
    cK
    chlt
    cW
    ltrneq2.h
    @63
    ltrneq2.t
    ltrnlaut
    syl2anc
    @57
    @28
    @2
    @4
    @18
    @66
    @41
    @42
    @58
    @16
    cT
    cG
    cH
    cK
    chlt
    cW
    @12
    @43
    ltrneq2.h
    ltrneq2.t
    ltrncl
    #
    syl3anc
    @16
    cG
    @59
    cK
    @21
    chlt
    @20
    @14
    @43
    @49
    @63
    lautcnvle
    syl22anc
    3bitr4d
    3exp2
    imp
    ralrimdv
    @19
    @0
    @61
    @66
    @25
    @15
    wb
    @0
    @1
    @3
    @4
    @18
    simpl1l
    @19
    @2
    @3
    @18
    @61
    @2
    @3
    @4
    @18
    simpl1
    #
    @2
    @3
    @4
    @18
    simpl2
    @5
    @18
    simpr
    #
    @64
    syl3anc
    @19
    @2
    @4
    @18
    @66
    @68
    @2
    @3
    @4
    @18
    simpl3
    @69
    @67
    syl3anc
    cA
    @16
    cK
    @21
    @13
    @14
    vq
    @43
    @49
    ltrneq2.a
    hlateq
    syl3anc
    sylibd
    ralrimdva
    @5
    cF
    @16
    wfn
    #
    cG
    @16
    wfn
    #
    @11
    @17
    wb
    @5
    @53
    @70
    @2
    @3
    @53
    @4
    @55
    3adant3
    @16
    @16
    cF
    f1ofn
    syl
    @5
    @39
    @71
    @2
    @4
    @39
    @3
    @44
    3adant2
    @16
    @16
    cG
    f1ofn
    syl
    vx
    @16
    cF
    cG
    eqfnfv
    syl2anc
    sylibrd
    @11
    @9
    vp
    cA
    @6
    cF
    cG
    fveq1
    ralrimivw
    impbid1
end
