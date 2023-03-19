include "clat.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "crab.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "ssrab2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "cbs.mm"
include "eqid.mm"
include "atbase.mm"
include "anim12i.mm"
include "latjcl.mm"
include "3expb.mm"
include "sylan2.mm"
include "eleq2.mm"
include "breq1.mm"
include "elrab.mm"
include "anim1i.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "anim12d.mm"
include "an4.mm"
include "syl6ib.mm"
include "imp.mm"
include "anim2i.mm"
include "anassrs.mm"
include "w3a.mm"
include "latjle12.mm"
include "biimpd.mm"
include "3exp2.mm"
include "impd.mm"
include "com23.mm"
include "imp43.mm"
include "adantr.mm"
include "3expib.mm"
include "lattr.mm"
include "com24.mm"
include "syl5d.mm"
include "imp41.mm"
include "adantlrr.mm"
include "mpan2d.mm"
include "syl2an.mm"
include "simpr.mm"
include "jctild.mm"
include "wb.mm"
include "syl6bb.mm"
include "ad3antlr.mm"
include "sylibrd.mm"
include "ralrimiva.mm"
include "ralrimivva.mm"
include "ex.mm"
include "syldan.mm"
include "jcad.mm"
include "adantld.mm"
include "rexlimdvva.mm"
include "isline.mm"
include "ispsubsp.mm"
include "3imtr4d.mm"

theorem linepsubN
  let cS: class S
  let cK: class K
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume linepsub.n: |- N = ( Lines ` K )
  assume linepsub.s: |- S = ( PSubSp ` K )


  assert |- ( ( K e. Lat /\ X e. N ) -> X e. S )

  proof
    cK
    clat
    wcel
    #
    cX
    cN
    wcel
    #
    cX
    cS
    wcel
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    cX
    vc
    cv
    #
    @3
    @4
    cK
    cjn
    cfv
    #
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    vc
    cK
    catm
    cfv
    #
    crab
    #
    wceq
    #
    wa
    #
    vb
    @11
    wrex
    va
    @11
    wrex
    cX
    @11
    wss
    #
    vr
    cv
    #
    vp
    cv
    #
    vq
    cv
    #
    @7
    co
    #
    @9
    wbr
    #
    @16
    cX
    wcel
    #
    wi
    #
    vr
    @11
    wral
    #
    vq
    cX
    wral
    vp
    cX
    wral
    #
    wa
    #
    @1
    @2
    @0
    @14
    @25
    va
    vb
    @11
    @11
    @0
    @3
    @11
    wcel
    #
    @4
    @11
    wcel
    #
    wa
    #
    wa
    #
    @13
    @25
    @5
    @29
    @13
    @15
    @24
    @13
    @15
    wi
    @29
    @13
    @15
    @12
    @11
    wss
    @10
    vc
    @11
    ssrab2
    cX
    @12
    @11
    sseq1
    mpbiri
    a1i
    @0
    @28
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    @13
    @24
    wi
    @28
    @0
    @3
    @30
    wcel
    #
    @4
    @30
    wcel
    #
    wa
    @31
    @26
    @32
    @27
    @33
    @11
    @30
    @3
    cK
    @30
    eqid
    #
    @11
    eqid
    #
    atbase
    @11
    @30
    @4
    cK
    @34
    @35
    atbase
    anim12i
    @0
    @32
    @33
    @31
    @30
    @7
    cK
    @3
    @4
    @34
    @7
    eqid
    #
    latjcl
    3expb
    sylan2
    @0
    @31
    wa
    #
    @13
    @24
    @37
    @13
    wa
    #
    @23
    vp
    vq
    cX
    cX
    @38
    @17
    cX
    wcel
    #
    @18
    cX
    wcel
    #
    wa
    #
    wa
    #
    @22
    vr
    @11
    @42
    @16
    @11
    wcel
    #
    wa
    #
    @20
    @43
    @16
    @8
    @9
    wbr
    #
    wa
    #
    @21
    @44
    @20
    @45
    @43
    @42
    @37
    @17
    @30
    wcel
    #
    @18
    @30
    wcel
    #
    wa
    #
    @17
    @8
    @9
    wbr
    #
    @18
    @8
    @9
    wbr
    #
    wa
    #
    wa
    #
    wa
    #
    @16
    @30
    wcel
    #
    @20
    @45
    wi
    @43
    @37
    @13
    @41
    @54
    @13
    @41
    wa
    @53
    @37
    @13
    @41
    @53
    @13
    @41
    @47
    @50
    wa
    #
    @48
    @51
    wa
    #
    wa
    @53
    @13
    @39
    @56
    @40
    @57
    @13
    @39
    @17
    @12
    wcel
    #
    @56
    cX
    @12
    @17
    eleq2
    @58
    @17
    @11
    wcel
    #
    @50
    wa
    @56
    @10
    @50
    vc
    @17
    @11
    @6
    @17
    @8
    @9
    breq1
    elrab
    @59
    @47
    @50
    @11
    @30
    @17
    cK
    @34
    @35
    atbase
    anim1i
    sylbi
    syl6bi
    @13
    @40
    @18
    @12
    wcel
    #
    @57
    cX
    @12
    @18
    eleq2
    @60
    @18
    @11
    wcel
    #
    @51
    wa
    @57
    @10
    @51
    vc
    @18
    @11
    @6
    @18
    @8
    @9
    breq1
    elrab
    @61
    @48
    @51
    @11
    @30
    @18
    cK
    @34
    @35
    atbase
    anim1i
    sylbi
    syl6bi
    anim12d
    @47
    @50
    @48
    @51
    an4
    syl6ib
    imp
    anim2i
    anassrs
    @11
    @30
    @16
    cK
    @34
    @35
    atbase
    @54
    @55
    wa
    @20
    @19
    @8
    @9
    wbr
    #
    @45
    @54
    @62
    @55
    @0
    @31
    @49
    @52
    @62
    @0
    @49
    @31
    @52
    @62
    wi
    #
    @0
    @47
    @48
    @31
    @63
    wi
    @0
    @47
    @48
    @31
    @63
    @0
    @47
    @48
    @31
    w3a
    wa
    @52
    @62
    @30
    @7
    cK
    @9
    @17
    @18
    @8
    @34
    @9
    eqid
    #
    @36
    latjle12
    biimpd
    3exp2
    impd
    com23
    imp43
    adantr
    @37
    @49
    @55
    @20
    @62
    wa
    @45
    wi
    #
    @52
    @0
    @31
    @49
    @55
    @65
    @0
    @49
    @19
    @30
    wcel
    #
    @31
    @55
    @65
    wi
    @0
    @47
    @48
    @66
    @30
    @7
    cK
    @17
    @18
    @34
    @36
    latjcl
    3expib
    @0
    @55
    @66
    @31
    @65
    @0
    @55
    @66
    @31
    @65
    @30
    cK
    @9
    @16
    @19
    @8
    @34
    @64
    lattr
    3exp2
    com24
    syl5d
    imp41
    adantlrr
    mpan2d
    syl2an
    @42
    @43
    simpr
    jctild
    @13
    @21
    @46
    wb
    @37
    @41
    @43
    @13
    @21
    @16
    @12
    wcel
    @46
    cX
    @12
    @16
    eleq2
    @10
    @45
    vc
    @16
    @11
    @6
    @16
    @8
    @9
    breq1
    elrab
    syl6bb
    ad3antlr
    sylibrd
    ralrimiva
    ralrimivva
    ex
    syldan
    jcad
    adantld
    rexlimdvva
    @11
    clat
    @7
    cK
    @9
    cN
    cX
    vb
    va
    vc
    @64
    @36
    @35
    linepsub.n
    isline
    @11
    clat
    cS
    @7
    cK
    @9
    cX
    vr
    vq
    vp
    @64
    @36
    @35
    linepsub.s
    ispsubsp
    3imtr4d
    imp
end
