include "cn.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "cuz.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rexbidv.mm"
include "imbi2d.mm"
include "c0.mm"
include "wne.mm"
include "1nn.mm"
include "ne0ii.mm"
include "ffvelrn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "adantr.mm"
include "peano2nn.mm"
include "adantl.mm"
include "cle.mm"
include "cr.mm"
include "nnre.mm"
include "ad2antrr.mm"
include "nnred.mm"
include "adantlr.mm"
include "adantll.mm"
include "1red.mm"
include "leadd1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "rspcv.mm"
include "imdistani.mm"
include "wb.mm"
include "sylan2.mm"
include "nnltp1le.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "anasss.mm"
include "anass1rs.mm"
include "peano2re.mm"
include "syl.mm"
include "letr.mm"
include "syl3anc.mm"
include "adantlrr.mm"
include "mpan2d.mm"
include "sylbid.mm"
include "cz.mm"
include "nnz.mm"
include "nnzd.mm"
include "eluz.mm"
include "syl2an.mm"
include "adantrlr.mm"
include "anassrs.mm"
include "peano2zd.mm"
include "3imtr4d.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "cbvrexv.mm"
include "syl6ib.mm"
include "ex.mm"
include "a2d.mm"
include "nnind.mm"
include "com12.mm"
include "3impia.mm"

theorem incsequz
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vp: setvar p
  let vq: setvar q

  disjoint F m
  disjoint F n
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint F k
  disjoint F p
  disjoint F q
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint m p
  disjoint m q
  disjoint n p
  disjoint n q
  disjoint p q
  disjoint A k
  disjoint A p
  disjoint A q
  assert |- ( ( F : NN --> NN /\ A. m e. NN ( F ` m ) < ( F ` ( m + 1 ) ) /\ A e. NN ) -> E. n e. NN ( F ` n ) e. ( ZZ>= ` A ) )

  proof
    cn
    cn
    cF
    wf
    #
    vm
    cv
    #
    cF
    cfv
    #
    @1
    c1
    caddc
    co
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vm
    cn
    wral
    #
    cA
    cn
    wcel
    #
    vn
    cv
    #
    cF
    cfv
    #
    cA
    cuz
    cfv
    #
    wcel
    #
    vn
    cn
    wrex
    #
    @7
    @0
    @6
    wa
    #
    @12
    @13
    @9
    vp
    cv
    #
    cuz
    cfv
    #
    wcel
    #
    vn
    cn
    wrex
    #
    wi
    @13
    @9
    c1
    cuz
    cfv
    #
    wcel
    #
    vn
    cn
    wrex
    #
    wi
    @13
    @9
    vq
    cv
    #
    cuz
    cfv
    #
    wcel
    #
    vn
    cn
    wrex
    #
    wi
    @13
    @9
    @21
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    vn
    cn
    wrex
    #
    wi
    @13
    @12
    wi
    vp
    vq
    cA
    @14
    c1
    wceq
    #
    @17
    @20
    @13
    @29
    @16
    @19
    vn
    cn
    @29
    @15
    @18
    @9
    @14
    c1
    cuz
    fveq2
    eleq2d
    rexbidv
    imbi2d
    @14
    @21
    wceq
    #
    @17
    @24
    @13
    @30
    @16
    @23
    vn
    cn
    @30
    @15
    @22
    @9
    @14
    @21
    cuz
    fveq2
    eleq2d
    rexbidv
    imbi2d
    @14
    @25
    wceq
    #
    @17
    @28
    @13
    @31
    @16
    @27
    vn
    cn
    @31
    @15
    @26
    @9
    @14
    @25
    cuz
    fveq2
    eleq2d
    rexbidv
    imbi2d
    @14
    cA
    wceq
    #
    @17
    @12
    @13
    @32
    @16
    @11
    vn
    cn
    @32
    @15
    @10
    @9
    @14
    cA
    cuz
    fveq2
    eleq2d
    rexbidv
    imbi2d
    @0
    @20
    @6
    @0
    cn
    c0
    wne
    @19
    vn
    cn
    wral
    @20
    c1
    cn
    1nn
    ne0ii
    @0
    @19
    vn
    cn
    @0
    @8
    cn
    wcel
    #
    wa
    #
    @9
    cn
    wcel
    #
    @19
    cn
    cn
    @8
    cF
    ffvelrn
    #
    @9
    elnnuz
    sylib
    ralrimiva
    @19
    vn
    cn
    r19.2z
    sylancr
    adantr
    @21
    cn
    wcel
    #
    @13
    @24
    @28
    @37
    @13
    @24
    @28
    wi
    @37
    @13
    wa
    #
    @24
    vk
    cv
    #
    cF
    cfv
    #
    @26
    wcel
    #
    vk
    cn
    wrex
    #
    @28
    @38
    @23
    @42
    vn
    cn
    @38
    @33
    wa
    #
    @8
    c1
    caddc
    co
    #
    cn
    wcel
    #
    @23
    @44
    cF
    cfv
    #
    @26
    wcel
    #
    @42
    @33
    @45
    @38
    @8
    peano2nn
    #
    adantl
    @43
    @21
    @9
    cle
    wbr
    #
    @25
    @46
    cle
    wbr
    #
    @23
    @47
    @43
    @49
    @25
    @9
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @50
    @43
    @21
    @9
    c1
    @37
    @21
    cr
    wcel
    #
    @13
    @33
    @21
    nnre
    #
    ad2antrr
    @13
    @33
    @9
    cr
    wcel
    #
    @37
    @0
    @33
    @55
    @6
    @34
    @9
    @36
    nnred
    adantlr
    adantll
    @43
    1red
    leadd1d
    @43
    @52
    @51
    @46
    cle
    wbr
    #
    @50
    @13
    @33
    @56
    @37
    @0
    @33
    @6
    @56
    @33
    @6
    wa
    @0
    @33
    @9
    @46
    clt
    wbr
    #
    wa
    @56
    @33
    @6
    @57
    @5
    @57
    vm
    @8
    cn
    @1
    @8
    wceq
    #
    @2
    @9
    @4
    @46
    clt
    @1
    @8
    cF
    fveq2
    @58
    @3
    @44
    cF
    @1
    @8
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    rspcv
    imdistani
    @0
    @33
    @57
    @56
    @34
    @57
    @56
    @34
    @35
    @46
    cn
    wcel
    #
    @57
    @56
    wb
    @36
    @33
    @0
    @45
    @59
    @48
    cn
    cn
    @44
    cF
    ffvelrn
    #
    sylan2
    @9
    @46
    nnltp1le
    syl2anc
    biimpa
    anasss
    sylan2
    anass1rs
    adantll
    @37
    @0
    @33
    @52
    @56
    wa
    @50
    wi
    #
    @6
    @37
    @0
    wa
    @33
    wa
    @25
    cr
    wcel
    #
    @51
    cr
    wcel
    #
    @46
    cr
    wcel
    #
    @61
    @37
    @62
    @0
    @33
    @37
    @53
    @62
    @54
    @21
    peano2re
    syl
    ad2antrr
    @0
    @33
    @63
    @37
    @34
    @51
    @34
    @35
    @51
    cn
    wcel
    @36
    @9
    peano2nn
    syl
    nnred
    adantll
    @0
    @33
    @64
    @37
    @33
    @0
    @45
    @64
    @48
    @0
    @45
    wa
    #
    @46
    @60
    nnred
    sylan2
    adantll
    @25
    @51
    @46
    letr
    syl3anc
    adantlrr
    mpan2d
    sylbid
    @37
    @13
    @33
    @23
    @49
    wb
    #
    @37
    @0
    @33
    @66
    @6
    @37
    @21
    cz
    wcel
    @9
    cz
    wcel
    @66
    @34
    @21
    nnz
    #
    @34
    @9
    @36
    nnzd
    @21
    @9
    eluz
    syl2an
    adantrlr
    anassrs
    @37
    @13
    @33
    @47
    @50
    wb
    #
    @37
    @0
    @33
    @68
    @6
    @37
    @25
    cz
    wcel
    @46
    cz
    wcel
    #
    @68
    @34
    @37
    @21
    @67
    peano2zd
    @33
    @0
    @45
    @69
    @48
    @65
    @46
    @60
    nnzd
    sylan2
    @25
    @46
    eluz
    syl2an
    adantrlr
    anassrs
    3imtr4d
    @41
    @47
    vk
    @44
    cn
    @39
    @44
    wceq
    @40
    @46
    @26
    @39
    @44
    cF
    fveq2
    eleq1d
    rspcev
    syl6an
    rexlimdva
    @41
    @27
    vk
    vn
    cn
    @39
    @8
    wceq
    @40
    @9
    @26
    @39
    @8
    cF
    fveq2
    eleq1d
    cbvrexv
    syl6ib
    ex
    a2d
    nnind
    com12
    3impia
end
