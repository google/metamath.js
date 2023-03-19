include "ctos.mm"
include "wcel.mm"
include "carchi.mm"
include "wa.mm"
include "csubmnd.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "cv.mm"
include "cplt.mm"
include "wbr.mm"
include "cmg.mm"
include "cple.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "cmnd.mm"
include "wb.mm"
include "submrcl.mm"
include "eqid.mm"
include "isarchi2.mm"
include "sylan2.mm"
include "biimpa.mm"
include "an32s.mm"
include "wss.mm"
include "submbas.mm"
include "submss.mm"
include "eqsstr3d.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "syl.mm"
include "adantl.mm"
include "wceq.mm"
include "subm0.mm"
include "ad2antrr.mm"
include "cid.mm"
include "cdif.mm"
include "ressle.mm"
include "difeq1d.mm"
include "pltfval.mm"
include "submmnd.mm"
include "3eqtr4d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "ad3antrrr.mm"
include "cn0.mm"
include "simplll.mm"
include "simpr.mm"
include "nnnn0d.mm"
include "simpllr.mm"
include "eleqtrrd.mm"
include "submmulg.mm"
include "syl3anc.mm"
include "rexbidva.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "sylibd.mm"
include "mpd.mm"
include "resstos.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "mpbird.mm"

theorem submarchi
  let cA: class A
  let cW: class W
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( W e. Toset /\ W e. Archi ) /\ A e. ( SubMnd ` W ) ) -> ( W |`s A ) e. Archi )

  proof
    cW
    ctos
    wcel
    #
    cW
    carchi
    wcel
    #
    wa
    #
    cA
    cW
    csubmnd
    cfv
    #
    wcel
    #
    wa
    #
    cW
    cA
    cress
    co
    #
    carchi
    wcel
    #
    @6
    c0g
    cfv
    #
    vx
    cv
    #
    @6
    cplt
    cfv
    #
    wbr
    #
    vy
    cv
    #
    vn
    cv
    #
    @9
    @6
    cmg
    cfv
    #
    co
    #
    @6
    cple
    cfv
    #
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    #
    vy
    @6
    cbs
    cfv
    #
    wral
    #
    vx
    @20
    wral
    #
    @5
    cW
    c0g
    cfv
    #
    @9
    cW
    cplt
    cfv
    #
    wbr
    #
    @12
    @13
    @9
    cW
    cmg
    cfv
    #
    co
    #
    cW
    cple
    cfv
    #
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    #
    vy
    cW
    cbs
    cfv
    #
    wral
    #
    vx
    @32
    wral
    #
    @22
    @0
    @4
    @1
    @34
    @0
    @4
    wa
    #
    @1
    @34
    @4
    @0
    cW
    cmnd
    wcel
    #
    @1
    @34
    wb
    cA
    cW
    submrcl
    #
    vx
    vy
    @32
    @24
    @26
    vn
    @28
    cW
    @23
    @32
    eqid
    #
    @23
    eqid
    #
    @26
    eqid
    #
    @28
    eqid
    #
    @24
    eqid
    #
    isarchi2
    sylan2
    biimpa
    an32s
    @5
    @34
    @31
    vy
    @20
    wral
    #
    vx
    @20
    wral
    #
    @22
    @4
    @34
    @44
    wi
    #
    @2
    @4
    @20
    @32
    wss
    #
    @45
    @4
    @20
    cA
    @32
    cA
    @6
    cW
    @6
    eqid
    #
    submbas
    #
    @32
    cA
    cW
    @38
    submss
    eqsstr3d
    @46
    @34
    @43
    vx
    @32
    wral
    @44
    @46
    @33
    @43
    vx
    @32
    @31
    vy
    @20
    @32
    ssralv
    ralimdv
    @43
    vx
    @20
    @32
    ssralv
    syld
    syl
    adantl
    @4
    @44
    @22
    wb
    @2
    @4
    @43
    @21
    vx
    @20
    @4
    @9
    @20
    wcel
    #
    wa
    #
    @31
    @19
    vy
    @20
    @50
    @12
    @20
    wcel
    #
    wa
    #
    @25
    @11
    @30
    @18
    @52
    @23
    @8
    @9
    @9
    @24
    @10
    @4
    @23
    @8
    wceq
    @49
    @51
    cA
    @6
    cW
    @23
    @47
    @39
    subm0
    ad2antrr
    @4
    @24
    @10
    wceq
    @49
    @51
    @4
    @28
    cid
    cdif
    #
    @16
    cid
    cdif
    #
    @24
    @10
    @4
    @28
    @16
    cid
    cA
    cW
    @28
    @3
    @6
    @47
    @41
    ressle
    #
    difeq1d
    @4
    @36
    @24
    @53
    wceq
    @37
    cmnd
    @24
    cW
    @28
    @41
    @42
    pltfval
    syl
    @4
    @6
    cmnd
    wcel
    #
    @10
    @54
    wceq
    cA
    @6
    cW
    @47
    submmnd
    #
    cmnd
    @10
    @6
    @16
    @16
    eqid
    #
    @10
    eqid
    #
    pltfval
    syl
    3eqtr4d
    ad2antrr
    @52
    @9
    eqidd
    breq123d
    @52
    @29
    @17
    vn
    cn
    @52
    @13
    cn
    wcel
    #
    wa
    #
    @12
    @12
    @27
    @15
    @28
    @16
    @61
    @12
    eqidd
    @4
    @28
    @16
    wceq
    @49
    @51
    @60
    @55
    ad3antrrr
    @61
    @4
    @13
    cn0
    wcel
    @9
    cA
    wcel
    @27
    @15
    wceq
    @4
    @49
    @51
    @60
    simplll
    #
    @61
    @13
    @52
    @60
    simpr
    nnnn0d
    @61
    @9
    @20
    cA
    @4
    @49
    @51
    @60
    simpllr
    @61
    @4
    cA
    @20
    wceq
    @62
    @48
    syl
    eleqtrrd
    cA
    @26
    @14
    cW
    @6
    @13
    @9
    @40
    @47
    @14
    eqid
    #
    submmulg
    syl3anc
    breq123d
    rexbidva
    imbi12d
    ralbidva
    ralbidva
    adantl
    sylibd
    mpd
    @0
    @4
    @7
    @22
    wb
    #
    @1
    @35
    @6
    ctos
    wcel
    @56
    @64
    cA
    cW
    @3
    resstos
    @4
    @56
    @0
    @57
    adantl
    vx
    vy
    @20
    @10
    @14
    vn
    @16
    @6
    @8
    @20
    eqid
    @8
    eqid
    @63
    @58
    @59
    isarchi2
    syl2anc
    adantlr
    mpbird
end
