include "corng.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "crg.mm"
include "wa.mm"
include "cogrp.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "cmulr.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "simpr.mm"
include "cgrp.mm"
include "comnd.mm"
include "ringgrp.mm"
include "adantl.mm"
include "cmnd.mm"
include "orngogrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "syl.mm"
include "ringmnd.mm"
include "submomnd.mm"
include "syl2an.mm"
include "sylanbrc.mm"
include "simp-4l.mm"
include "wss.mm"
include "cvv.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "reldmress.mm"
include "ovprc2.mm"
include "fveq2d.mm"
include "base0.mm"
include "syl6eqr.mm"
include "wne.mm"
include "cur.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ne0i.mm"
include "ad2antlr.mm"
include "neneqd.mm"
include "condan.mm"
include "cin.mm"
include "ressbas.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "sseldd.mm"
include "simprl.mm"
include "wb.mm"
include "csubg.mm"
include "orngring.mm"
include "adantr.mm"
include "ressinbas.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqeltrrd.mm"
include "issubg.mm"
include "syl3anbrc.mm"
include "subg0.mm"
include "eqtr4d.mm"
include "ad2antrr.mm"
include "ressle.mm"
include "eqidd.mm"
include "breq123d.mm"
include "mpbird.mm"
include "simplr.mm"
include "simprr.mm"
include "orngmul.mm"
include "syl122anc.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "mpbid.mm"
include "ex.mm"
include "anasss.mm"
include "ralrimivva.mm"
include "isorng.mm"

theorem suborng
  let cA: class A
  let cR: class R
  let va: setvar a
  let vb: setvar b


  assert |- ( ( R e. oRing /\ ( R |`s A ) e. Ring ) -> ( R |`s A ) e. oRing )

  proof
    cR
    corng
    wcel
    #
    cR
    cA
    cress
    co
    #
    crg
    wcel
    #
    wa
    #
    @2
    @1
    cogrp
    wcel
    #
    @1
    c0g
    cfv
    #
    va
    cv
    #
    @1
    cple
    cfv
    #
    wbr
    #
    @5
    vb
    cv
    #
    @7
    wbr
    #
    wa
    #
    @5
    @6
    @9
    @1
    cmulr
    cfv
    #
    co
    #
    @7
    wbr
    #
    wi
    #
    vb
    @1
    cbs
    cfv
    #
    wral
    va
    @16
    wral
    @1
    corng
    wcel
    @0
    @2
    simpr
    @3
    @1
    cgrp
    wcel
    #
    @1
    comnd
    wcel
    #
    @4
    @2
    @17
    @0
    @1
    ringgrp
    adantl
    #
    @0
    cR
    comnd
    wcel
    #
    @1
    cmnd
    wcel
    @18
    @2
    @0
    cR
    cogrp
    wcel
    #
    @20
    cR
    orngogrp
    @21
    cR
    cgrp
    wcel
    #
    @20
    cR
    isogrp
    simprbi
    syl
    @1
    ringmnd
    cA
    cR
    submomnd
    syl2an
    @1
    isogrp
    sylanbrc
    @3
    @15
    va
    vb
    @16
    @16
    @3
    @6
    @16
    wcel
    #
    @9
    @16
    wcel
    #
    @15
    @3
    @23
    wa
    #
    @24
    wa
    #
    @11
    @14
    @26
    @11
    wa
    #
    cR
    c0g
    cfv
    #
    @6
    @9
    cR
    cmulr
    cfv
    #
    co
    #
    cR
    cple
    cfv
    #
    wbr
    #
    @14
    @27
    @0
    @6
    cR
    cbs
    cfv
    #
    wcel
    @28
    @6
    @31
    wbr
    #
    @9
    @33
    wcel
    @28
    @9
    @31
    wbr
    #
    @32
    @0
    @2
    @23
    @24
    @11
    simp-4l
    @27
    @16
    @33
    @6
    @3
    @16
    @33
    wss
    #
    @23
    @24
    @11
    @3
    cA
    cvv
    wcel
    #
    @36
    @3
    @37
    @16
    c0
    wceq
    @3
    @37
    wn
    #
    wa
    #
    @16
    c0
    cbs
    cfv
    #
    c0
    @38
    @16
    @40
    wceq
    @3
    @38
    @1
    c0
    cbs
    cR
    cA
    cress
    reldmress
    ovprc2
    fveq2d
    adantl
    base0
    syl6eqr
    @39
    @16
    c0
    @2
    @16
    c0
    wne
    #
    @0
    @38
    @2
    @1
    cur
    cfv
    #
    @16
    wcel
    @41
    @16
    @1
    @42
    @16
    eqid
    #
    @42
    eqid
    ringidcl
    @16
    @42
    ne0i
    syl
    ad2antlr
    neneqd
    condan
    #
    @37
    @16
    cA
    @33
    cin
    #
    @33
    cA
    @33
    @1
    cvv
    cR
    @1
    eqid
    #
    @33
    eqid
    #
    ressbas
    #
    cA
    @33
    inss2
    syl6eqssr
    syl
    #
    ad3antrrr
    #
    @3
    @23
    @24
    @11
    simpllr
    sseldd
    @27
    @34
    @8
    @26
    @8
    @10
    simprl
    @26
    @34
    @8
    wb
    @11
    @26
    @28
    @5
    @6
    @6
    @31
    @7
    @3
    @28
    @5
    wceq
    #
    @23
    @24
    @3
    @28
    cR
    @16
    cress
    co
    #
    c0g
    cfv
    #
    @5
    @3
    @16
    cR
    csubg
    cfv
    wcel
    #
    @28
    @53
    wceq
    @3
    @22
    @36
    @52
    cgrp
    wcel
    @54
    @0
    @22
    @2
    @0
    cR
    crg
    wcel
    @22
    cR
    orngring
    cR
    ringgrp
    syl
    adantr
    @49
    @3
    @1
    @52
    cgrp
    @3
    @37
    @1
    @52
    wceq
    @44
    @37
    @1
    cR
    @45
    cress
    co
    @52
    cA
    @33
    cR
    cvv
    @47
    ressinbas
    @37
    @45
    @16
    cR
    cress
    @48
    oveq2d
    eqtrd
    syl
    #
    @19
    eqeltrrd
    @33
    @16
    cR
    @47
    issubg
    syl3anbrc
    @16
    cR
    @52
    @28
    @52
    eqid
    @28
    eqid
    #
    subg0
    syl
    @3
    @1
    @52
    c0g
    @55
    fveq2d
    eqtr4d
    ad2antrr
    #
    @26
    @37
    @31
    @7
    wceq
    #
    @3
    @37
    @23
    @24
    @44
    ad2antrr
    #
    cA
    cR
    @31
    cvv
    @1
    @46
    @31
    eqid
    #
    ressle
    syl
    #
    @26
    @6
    eqidd
    breq123d
    adantr
    mpbird
    @27
    @16
    @33
    @9
    @50
    @25
    @24
    @11
    simplr
    sseldd
    @27
    @35
    @10
    @26
    @8
    @10
    simprr
    @26
    @35
    @10
    wb
    @11
    @26
    @28
    @5
    @9
    @9
    @31
    @7
    @57
    @61
    @26
    @9
    eqidd
    breq123d
    adantr
    mpbird
    @33
    cR
    @29
    @31
    @6
    @9
    @28
    @47
    @60
    @56
    @29
    eqid
    #
    orngmul
    syl122anc
    @27
    @28
    @5
    @30
    @13
    @31
    @7
    @26
    @51
    @11
    @57
    adantr
    @26
    @58
    @11
    @61
    adantr
    @27
    @29
    @12
    @6
    @9
    @27
    @37
    @29
    @12
    wceq
    @26
    @37
    @11
    @59
    adantr
    cA
    cR
    @1
    @29
    cvv
    @46
    @62
    ressmulr
    syl
    oveqd
    breq123d
    mpbid
    ex
    anasss
    ralrimivva
    @16
    @1
    @12
    @7
    @5
    va
    vb
    @43
    @5
    eqid
    @12
    eqid
    @7
    eqid
    isorng
    syl3anbrc
end
