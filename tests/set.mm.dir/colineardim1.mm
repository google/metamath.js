include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cbtwn.mm"
include "w3o.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "coprab.mm"
include "ccnv.mm"
include "df-colinear.mm"
include "breqi.mm"
include "cvv.mm"
include "wb.mm"
include "simpr1.mm"
include "opex.mm"
include "brcnvg.mm"
include "sylancl.mm"
include "df-br.mm"
include "wceq.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "opeq1.mm"
include "breq2d.mm"
include "breq1.mm"
include "opeq2.mm"
include "3orbi123d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "3anbi3d.mm"
include "3anbi1d.mm"
include "eloprabg.mm"
include "3comr.mm"
include "adantl.mm"
include "simpl.mm"
include "simp2.mm"
include "anim2i.mm"
include "3simpa.mm"
include "axdimuniq.mm"
include "adantrrl.mm"
include "simprrl.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "syl2an.mm"
include "exp32.mm"
include "syl7.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "syl5bi.mm"

theorem colineardim1
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vn: setvar n


  assert |- ( ( N e. NN /\ ( A e. V /\ B e. ( EE ` N ) /\ C e. W ) ) -> ( A Colinear <. B , C >. -> A e. ( EE ` N ) ) )

  proof
    cA
    cB
    cC
    cop
    #
    ccolin
    wbr
    cA
    @0
    va
    cv
    #
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    vb
    cv
    #
    @3
    wcel
    #
    vc
    cv
    #
    @3
    wcel
    #
    w3a
    #
    @1
    @5
    @7
    cop
    #
    cbtwn
    wbr
    #
    @5
    @7
    @1
    cop
    #
    cbtwn
    wbr
    #
    @7
    @1
    @5
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    #
    vb
    vc
    va
    coprab
    #
    ccnv
    #
    wbr
    #
    cN
    cn
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cN
    cee
    cfv
    #
    wcel
    #
    cC
    cW
    wcel
    #
    w3a
    #
    wa
    #
    cA
    @24
    wcel
    #
    cA
    @0
    ccolin
    @20
    vn
    va
    vb
    vc
    df-colinear
    breqi
    @28
    @21
    @0
    cA
    @19
    wbr
    #
    @29
    @28
    @23
    @0
    cvv
    wcel
    @21
    @30
    wb
    @22
    @23
    @25
    @26
    simpr1
    cB
    cC
    opex
    cA
    @0
    cV
    cvv
    @19
    brcnvg
    sylancl
    @30
    @0
    cA
    cop
    @19
    wcel
    #
    @28
    @29
    @0
    cA
    @19
    df-br
    @28
    @31
    cA
    @3
    wcel
    #
    cB
    @3
    wcel
    #
    cC
    @3
    wcel
    #
    w3a
    #
    cA
    @0
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    #
    cbtwn
    wbr
    #
    cC
    cA
    cB
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    #
    @29
    @27
    @31
    @43
    wb
    #
    @22
    @25
    @26
    @23
    @44
    @18
    @4
    @33
    @8
    w3a
    #
    @1
    cB
    @7
    cop
    #
    cbtwn
    wbr
    #
    cB
    @12
    cbtwn
    wbr
    #
    @7
    @1
    cB
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    @4
    @33
    @34
    w3a
    #
    @1
    @0
    cbtwn
    wbr
    #
    cB
    cC
    @1
    cop
    #
    cbtwn
    wbr
    #
    cC
    @49
    cbtwn
    wbr
    #
    w3o
    #
    wa
    #
    vn
    cn
    wrex
    @43
    vb
    vc
    va
    cB
    cC
    cA
    @24
    cW
    cV
    @5
    cB
    wceq
    #
    @17
    @52
    vn
    cn
    @60
    @9
    @45
    @16
    @51
    @60
    @6
    @33
    @4
    @8
    @5
    cB
    @3
    eleq1
    3anbi2d
    @60
    @11
    @47
    @13
    @48
    @15
    @50
    @60
    @10
    @46
    @1
    cbtwn
    @5
    cB
    @7
    opeq1
    breq2d
    @5
    cB
    @12
    cbtwn
    breq1
    @60
    @14
    @49
    @7
    cbtwn
    @5
    cB
    @1
    opeq2
    breq2d
    3orbi123d
    anbi12d
    rexbidv
    @7
    cC
    wceq
    #
    @52
    @59
    vn
    cn
    @61
    @45
    @53
    @51
    @58
    @61
    @8
    @34
    @4
    @33
    @7
    cC
    @3
    eleq1
    3anbi3d
    @61
    @47
    @54
    @48
    @56
    @50
    @57
    @61
    @46
    @0
    @1
    cbtwn
    @7
    cC
    cB
    opeq2
    breq2d
    @61
    @12
    @55
    cB
    cbtwn
    @7
    cC
    @1
    opeq1
    breq2d
    @7
    cC
    @49
    cbtwn
    breq1
    3orbi123d
    anbi12d
    rexbidv
    @1
    cA
    wceq
    #
    @59
    @42
    vn
    cn
    @62
    @53
    @35
    @58
    @41
    @62
    @4
    @32
    @33
    @34
    @1
    cA
    @3
    eleq1
    3anbi1d
    @62
    @54
    @36
    @56
    @38
    @57
    @40
    @1
    cA
    @0
    cbtwn
    breq1
    @62
    @55
    @37
    cB
    cbtwn
    @1
    cA
    cC
    opeq2
    breq2d
    @62
    @49
    @39
    cC
    cbtwn
    @1
    cA
    cB
    opeq1
    breq2d
    3orbi123d
    anbi12d
    rexbidv
    eloprabg
    3comr
    adantl
    @28
    @42
    @29
    vn
    cn
    @42
    @35
    @28
    @2
    cn
    wcel
    #
    @29
    @35
    @41
    simpl
    @28
    @63
    @35
    @29
    @28
    @22
    @25
    wa
    #
    @63
    @32
    @33
    wa
    #
    wa
    #
    @29
    @63
    @35
    wa
    @27
    @25
    @22
    @23
    @25
    @26
    simp2
    anim2i
    @35
    @65
    @63
    @32
    @33
    @34
    3simpa
    anim2i
    @64
    @66
    wa
    #
    cN
    @2
    wceq
    #
    @29
    @64
    @63
    @33
    @68
    @32
    cB
    @2
    cN
    axdimuniq
    adantrrl
    @67
    @29
    @68
    @32
    @64
    @63
    @32
    @33
    simprrl
    @68
    @24
    @3
    cA
    cN
    @2
    cee
    fveq2
    eleq2d
    syl5ibrcom
    mpd
    syl2an
    exp32
    syl7
    rexlimdv
    sylbid
    syl5bi
    sylbid
    syl5bi
end
