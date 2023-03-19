include "clat.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "crab.mm"
include "eqid.mm"
include "pmapval.mm"
include "wss.mm"
include "cjn.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "breq1.mm"
include "elrab.mm"
include "atbase.mm"
include "anim1i.mm"
include "sylbi.mm"
include "anim12i.mm"
include "an4.mm"
include "sylib.mm"
include "anim2i.mm"
include "w3a.mm"
include "latjle12.mm"
include "biimpd.mm"
include "3exp2.mm"
include "impd.mm"
include "com23.mm"
include "imp43.mm"
include "adantr.mm"
include "latjcl.mm"
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
include "syl6ibr.mm"
include "ralrimiva.mm"
include "ralrimivva.mm"
include "ssrab2.mm"
include "jctil.mm"
include "wb.mm"
include "ispsubsp.mm"
include "mpbird.mm"
include "eqeltrd.mm"

theorem pmapsub
  let cB: class B
  let cS: class S
  let cK: class K
  let cM: class M
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vc: setvar c
  assume pmapsub.b: |- B = ( Base ` K )
  assume pmapsub.s: |- S = ( PSubSp ` K )
  assume pmapsub.m: |- M = ( pmap ` K )


  assert |- ( ( K e. Lat /\ X e. B ) -> ( M ` X ) e. S )

  proof
    cK
    clat
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cM
    cfv
    vc
    cv
    #
    cX
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
    cS
    @6
    cB
    clat
    cK
    @4
    cM
    cX
    vc
    pmapsub.b
    @4
    eqid
    #
    @6
    eqid
    #
    pmapsub.m
    pmapval
    @2
    @7
    cS
    wcel
    #
    @7
    @6
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
    cK
    cjn
    cfv
    #
    co
    #
    @4
    wbr
    #
    @12
    @7
    wcel
    #
    wi
    #
    vr
    @6
    wral
    #
    vq
    @7
    wral
    vp
    @7
    wral
    #
    wa
    #
    @2
    @21
    @11
    @2
    @20
    vp
    vq
    @7
    @7
    @2
    @13
    @7
    wcel
    #
    @14
    @7
    wcel
    #
    wa
    #
    wa
    #
    @19
    vr
    @6
    @26
    @12
    @6
    wcel
    #
    wa
    #
    @17
    @27
    @12
    cX
    @4
    wbr
    #
    wa
    @18
    @28
    @17
    @29
    @27
    @26
    @2
    @13
    cB
    wcel
    #
    @14
    cB
    wcel
    #
    wa
    #
    @13
    cX
    @4
    wbr
    #
    @14
    cX
    @4
    wbr
    #
    wa
    #
    wa
    #
    wa
    #
    @12
    cB
    wcel
    #
    @17
    @29
    wi
    @27
    @25
    @36
    @2
    @25
    @30
    @33
    wa
    #
    @31
    @34
    wa
    #
    wa
    @36
    @23
    @39
    @24
    @40
    @23
    @13
    @6
    wcel
    #
    @33
    wa
    @39
    @5
    @33
    vc
    @13
    @6
    @3
    @13
    cX
    @4
    breq1
    elrab
    @41
    @30
    @33
    @6
    cB
    @13
    cK
    pmapsub.b
    @9
    atbase
    anim1i
    sylbi
    @24
    @14
    @6
    wcel
    #
    @34
    wa
    @40
    @5
    @34
    vc
    @14
    @6
    @3
    @14
    cX
    @4
    breq1
    elrab
    @42
    @31
    @34
    @6
    cB
    @14
    cK
    pmapsub.b
    @9
    atbase
    anim1i
    sylbi
    anim12i
    @30
    @33
    @31
    @34
    an4
    sylib
    anim2i
    @6
    cB
    @12
    cK
    pmapsub.b
    @9
    atbase
    @37
    @38
    wa
    @17
    @16
    cX
    @4
    wbr
    #
    @29
    @37
    @43
    @38
    @0
    @1
    @32
    @35
    @43
    @0
    @32
    @1
    @35
    @43
    wi
    #
    @0
    @30
    @31
    @1
    @44
    wi
    @0
    @30
    @31
    @1
    @44
    @0
    @30
    @31
    @1
    w3a
    wa
    @35
    @43
    cB
    @15
    cK
    @4
    @13
    @14
    cX
    pmapsub.b
    @8
    @15
    eqid
    #
    latjle12
    biimpd
    3exp2
    impd
    com23
    imp43
    adantr
    @2
    @32
    @38
    @17
    @43
    wa
    @29
    wi
    #
    @35
    @0
    @1
    @32
    @38
    @46
    @0
    @32
    @16
    cB
    wcel
    #
    @1
    @38
    @46
    wi
    @0
    @30
    @31
    @47
    cB
    @15
    cK
    @13
    @14
    pmapsub.b
    @45
    latjcl
    3expib
    @0
    @38
    @47
    @1
    @46
    @0
    @38
    @47
    @1
    @46
    cB
    cK
    @4
    @12
    @16
    cX
    pmapsub.b
    @8
    lattr
    3exp2
    com24
    syl5d
    imp41
    adantlrr
    mpan2d
    syl2an
    @26
    @27
    simpr
    jctild
    @5
    @29
    vc
    @12
    @6
    @3
    @12
    cX
    @4
    breq1
    elrab
    syl6ibr
    ralrimiva
    ralrimivva
    @5
    vc
    @6
    ssrab2
    jctil
    @0
    @10
    @22
    wb
    @1
    @6
    clat
    cS
    @15
    cK
    @4
    @7
    vr
    vq
    vp
    @8
    @45
    @9
    pmapsub.s
    ispsubsp
    adantr
    mpbird
    eqeltrd
end
