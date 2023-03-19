include "c1st.mm"
include "ccom.mm"
include "cca.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "c2nd.mm"
include "wa.mm"
include "cbl.mm"
include "wss.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "cz.mm"
include "ssid.mm"
include "2a1i.mm"
include "eluznn.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "anassrs.mm"
include "sstr2.mm"
include "syl.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "com12.mm"
include "ad2ant2r.mm"
include "cop.mm"
include "cxp.mm"
include "wrel.mm"
include "relxp.mm"
include "wf.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "ffvelrnd.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "cxmt.mm"
include "cxr.mm"
include "cle.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "rpxrd.mm"
include "simpllr.mm"
include "simplrr.mm"
include "cr.mm"
include "rpre.mm"
include "ltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "ssbl.mm"
include "syl221anc.mm"
include "eqsstrd.mm"
include "syl5com.mm"
include "simprl.mm"
include "sylan.mm"
include "blcntr.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "ssel.mm"
include "syl6ci.mm"
include "wb.mm"
include "elbl2.mm"
include "syl22anc.mm"
include "sylibd.mm"
include "ex.mm"
include "mpdd.mm"
include "ralrimiv.mm"
include "expr.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "nnuz.mm"
include "1zzd.mm"
include "fvco3.mm"
include "1stcof.mm"
include "iscauf.mm"
include "mpbird.mm"

theorem caubl
  let wph: wff ph
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cX: class X
  let vr: setvar r
  let vk: setvar k
  let cA: class A
  let cJ: class J
  let cP: class P
  assume caubl.2: |- ( ph -> D e. ( *Met ` X ) )
  assume caubl.3: |- ( ph -> F : NN --> ( X X. RR+ ) )
  assume caubl.4: |- ( ph -> A. n e. NN ( ( ball ` D ) ` ( F ` ( n + 1 ) ) ) C_ ( ( ball ` D ) ` ( F ` n ) ) )
  assume caubl.5: |- ( ph -> A. r e. RR+ E. n e. NN ( 2nd ` ( F ` n ) ) < r )

  disjoint n ph
  disjoint n r
  disjoint D n
  disjoint D r
  disjoint F n
  disjoint F r
  disjoint ph r
  disjoint X n
  disjoint X r
  disjoint k r
  disjoint A k
  disjoint A r
  disjoint k n
  disjoint D k
  disjoint F k
  disjoint k ph
  disjoint X k
  disjoint J k
  disjoint P k
  assert |- ( ph -> ( 1st o. F ) e. ( Cau ` D ) )

  proof
    wph
    c1st
    cF
    ccom
    #
    cD
    cca
    cfv
    wcel
    vn
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    vk
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    cD
    co
    vr
    cv
    #
    clt
    wbr
    #
    vk
    @1
    cuz
    cfv
    #
    wral
    #
    vn
    cn
    wrex
    #
    vr
    crp
    wral
    #
    wph
    @2
    c2nd
    cfv
    #
    @7
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    vr
    crp
    wral
    @12
    caubl.5
    wph
    @15
    @11
    vr
    crp
    wph
    @7
    crp
    wcel
    #
    wa
    #
    @14
    @10
    vn
    cn
    @17
    @1
    cn
    wcel
    #
    @14
    @10
    @17
    @18
    @14
    wa
    #
    wa
    #
    @8
    vk
    @9
    @20
    @4
    @9
    wcel
    #
    @5
    cD
    cbl
    cfv
    #
    cfv
    #
    @2
    @22
    cfv
    #
    wss
    #
    @8
    wph
    @18
    @21
    @25
    wi
    @16
    @14
    @21
    wph
    @18
    wa
    #
    @25
    @26
    @7
    cF
    cfv
    #
    @22
    cfv
    #
    @24
    wss
    #
    wi
    @26
    @24
    @24
    wss
    #
    wi
    @26
    @25
    wi
    #
    @26
    @4
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @22
    cfv
    #
    @24
    wss
    #
    wi
    @31
    vr
    vk
    @1
    @4
    @7
    @1
    wceq
    #
    @29
    @30
    @26
    @36
    @28
    @24
    @24
    @36
    @27
    @2
    @22
    @7
    @1
    cF
    fveq2
    fveq2d
    sseq1d
    imbi2d
    @7
    @4
    wceq
    #
    @29
    @25
    @26
    @37
    @28
    @23
    @24
    @37
    @27
    @5
    @22
    @7
    @4
    cF
    fveq2
    fveq2d
    sseq1d
    imbi2d
    #
    @7
    @32
    wceq
    #
    @29
    @35
    @26
    @39
    @28
    @34
    @24
    @39
    @27
    @33
    @22
    @7
    @32
    cF
    fveq2
    fveq2d
    sseq1d
    imbi2d
    @38
    @30
    @1
    cz
    wcel
    @26
    @24
    ssid
    2a1i
    @21
    @26
    @25
    @35
    @26
    @21
    @25
    @35
    wi
    #
    @26
    @21
    wa
    @34
    @23
    wss
    #
    @40
    wph
    @18
    @21
    @41
    wph
    @1
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @22
    cfv
    #
    @24
    wss
    #
    vn
    cn
    wral
    @4
    cn
    wcel
    #
    @41
    @18
    @21
    wa
    caubl.4
    @4
    @1
    eluznn
    #
    @45
    @41
    vn
    @4
    cn
    @1
    @4
    wceq
    #
    @44
    @34
    @24
    @23
    @48
    @43
    @33
    @22
    @48
    @42
    @32
    cF
    @1
    @4
    c1
    caddc
    oveq1
    fveq2d
    fveq2d
    @48
    @2
    @5
    @22
    @1
    @4
    cF
    fveq2
    fveq2d
    sseq12d
    rspccva
    syl2an
    anassrs
    @34
    @23
    @24
    sstr2
    syl
    expcom
    a2d
    uzind4
    com12
    ad2ant2r
    @20
    @21
    @25
    @8
    wi
    @20
    @21
    wa
    #
    @25
    @6
    @3
    @7
    @22
    co
    #
    wcel
    #
    @8
    @49
    @25
    @23
    @50
    wss
    #
    @6
    @23
    wcel
    @51
    @49
    @24
    @50
    wss
    @25
    @52
    @49
    @24
    @3
    @13
    @22
    co
    #
    @50
    @49
    @24
    @3
    @13
    cop
    #
    @22
    cfv
    @53
    @49
    @2
    @54
    @22
    @49
    cX
    crp
    cxp
    #
    wrel
    #
    @2
    @55
    wcel
    #
    @2
    @54
    wceq
    cX
    crp
    relxp
    #
    @49
    cn
    @55
    @1
    cF
    wph
    cn
    @55
    cF
    wf
    #
    @16
    @19
    @21
    caubl.3
    ad3antrrr
    #
    @17
    @18
    @14
    @21
    simplrl
    ffvelrnd
    #
    @2
    @55
    1st2nd
    sylancr
    fveq2d
    @3
    @13
    @22
    df-ov
    syl6eqr
    @49
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @3
    cX
    wcel
    #
    @13
    cxr
    wcel
    @7
    cxr
    wcel
    #
    @13
    @7
    cle
    wbr
    #
    @53
    @50
    wss
    wph
    @62
    @16
    @19
    @21
    caubl.2
    ad3antrrr
    #
    @49
    @57
    @63
    @61
    @2
    cX
    crp
    xp1st
    syl
    #
    @49
    @13
    @49
    @57
    @13
    crp
    wcel
    #
    @61
    @2
    cX
    crp
    xp2nd
    syl
    #
    rpxrd
    @49
    @7
    wph
    @16
    @19
    @21
    simpllr
    #
    rpxrd
    #
    @49
    @14
    @65
    @17
    @18
    @14
    @21
    simplrr
    @49
    @68
    @16
    @14
    @65
    wi
    #
    @69
    @70
    @68
    @13
    cr
    wcel
    @7
    cr
    wcel
    @72
    @16
    @13
    rpre
    @7
    rpre
    @13
    @7
    ltle
    syl2an
    syl2anc
    mpd
    cD
    @3
    @13
    @7
    cX
    ssbl
    syl221anc
    eqsstrd
    @23
    @24
    @50
    sstr2
    syl5com
    @49
    @6
    @6
    @5
    c2nd
    cfv
    #
    @22
    co
    #
    @23
    @49
    @62
    @6
    cX
    wcel
    #
    @73
    crp
    wcel
    #
    @6
    @74
    wcel
    @66
    @49
    @5
    @55
    wcel
    #
    @75
    @49
    cn
    @55
    @4
    cF
    @60
    @20
    @18
    @21
    @46
    @17
    @18
    @14
    simprl
    @47
    sylan
    ffvelrnd
    #
    @5
    cX
    crp
    xp1st
    syl
    #
    @49
    @77
    @76
    @78
    @5
    cX
    crp
    xp2nd
    syl
    cD
    @6
    @73
    cX
    blcntr
    syl3anc
    @49
    @23
    @6
    @73
    cop
    #
    @22
    cfv
    @74
    @49
    @5
    @80
    @22
    @49
    @56
    @77
    @5
    @80
    wceq
    @58
    @78
    @5
    @55
    1st2nd
    sylancr
    fveq2d
    @6
    @73
    @22
    df-ov
    syl6eqr
    eleqtrrd
    @23
    @50
    @6
    ssel
    syl6ci
    @49
    @62
    @64
    @63
    @75
    @51
    @8
    wb
    @66
    @71
    @67
    @79
    @6
    cD
    @3
    @7
    cX
    elbl2
    syl22anc
    sylibd
    ex
    mpdd
    ralrimiv
    expr
    reximdva
    ralimdva
    mpd
    wph
    vr
    @6
    @3
    cD
    vn
    vk
    @0
    c1
    cX
    cn
    nnuz
    caubl.2
    wph
    1zzd
    wph
    @59
    @46
    @4
    @0
    cfv
    @6
    wceq
    caubl.3
    cn
    @55
    @4
    c1st
    cF
    fvco3
    sylan
    wph
    @59
    @18
    @1
    @0
    cfv
    @3
    wceq
    caubl.3
    cn
    @55
    @1
    c1st
    cF
    fvco3
    sylan
    wph
    @59
    cn
    cX
    @0
    wf
    caubl.3
    cn
    cX
    crp
    cF
    1stcof
    syl
    iscauf
    mpbird
end
