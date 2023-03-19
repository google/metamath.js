include "comnd.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "cmnd.mm"
include "wa.mm"
include "ctos.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "cplusg.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "simpr.mm"
include "cvv.mm"
include "omndtos.mm"
include "adantr.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "reldmress.mm"
include "ovprc2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "base0.mm"
include "syl6eqr.mm"
include "wne.mm"
include "c0g.mm"
include "eqid.mm"
include "mndidcl.mm"
include "ne0i.mm"
include "syl.mm"
include "ad2antlr.mm"
include "neneqd.mm"
include "condan.mm"
include "resstos.mm"
include "syl2anc.mm"
include "w3a.mm"
include "simplll.mm"
include "wss.mm"
include "cin.mm"
include "ressbas.mm"
include "inss2.mm"
include "syl6eqssr.mm"
include "ad2antrr.mm"
include "simplr1.mm"
include "sseldd.mm"
include "simplr2.mm"
include "simplr3.mm"
include "ressle.mm"
include "breqd.mm"
include "biimpar.mm"
include "omndadd.mm"
include "syl131anc.mm"
include "wb.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "breq123d.mm"
include "mpbid.mm"
include "ex.mm"
include "ralrimivvva.mm"
include "isomnd.mm"
include "syl3anbrc.mm"

theorem submomnd
  let cA: class A
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( M e. oMnd /\ ( M |`s A ) e. Mnd ) -> ( M |`s A ) e. oMnd )

  proof
    cM
    comnd
    wcel
    #
    cM
    cA
    cress
    co
    #
    cmnd
    wcel
    #
    wa
    #
    @2
    @1
    ctos
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    @1
    cple
    cfv
    #
    wbr
    #
    @5
    vc
    cv
    #
    @1
    cplusg
    cfv
    #
    co
    #
    @6
    @9
    @10
    co
    #
    @7
    wbr
    #
    wi
    #
    vc
    @1
    cbs
    cfv
    #
    wral
    vb
    @15
    wral
    va
    @15
    wral
    @1
    comnd
    wcel
    @0
    @2
    simpr
    @3
    cM
    ctos
    wcel
    #
    cA
    cvv
    wcel
    #
    @4
    @0
    @16
    @2
    cM
    omndtos
    adantr
    @3
    @17
    @15
    c0
    wceq
    @3
    @17
    wn
    #
    wa
    #
    @15
    c0
    cbs
    cfv
    #
    c0
    @18
    @15
    @20
    wceq
    @3
    @18
    @1
    c0
    cbs
    cM
    cA
    cress
    reldmress
    ovprc2
    fveq2d
    adantl
    base0
    syl6eqr
    @19
    @15
    c0
    @2
    @15
    c0
    wne
    #
    @0
    @18
    @2
    @1
    c0g
    cfv
    #
    @15
    wcel
    @21
    @15
    @1
    @22
    @15
    eqid
    #
    @22
    eqid
    mndidcl
    @15
    @22
    ne0i
    syl
    ad2antlr
    neneqd
    condan
    #
    cA
    cM
    cvv
    resstos
    syl2anc
    @3
    @14
    va
    vb
    vc
    @15
    @15
    @15
    @3
    @5
    @15
    wcel
    #
    @6
    @15
    wcel
    #
    @9
    @15
    wcel
    #
    w3a
    #
    wa
    #
    @8
    @13
    @29
    @8
    wa
    #
    @5
    @9
    cM
    cplusg
    cfv
    #
    co
    #
    @6
    @9
    @31
    co
    #
    cM
    cple
    cfv
    #
    wbr
    #
    @13
    @30
    @0
    @5
    cM
    cbs
    cfv
    #
    wcel
    @6
    @36
    wcel
    @9
    @36
    wcel
    @5
    @6
    @34
    wbr
    #
    @35
    @0
    @2
    @28
    @8
    simplll
    @30
    @15
    @36
    @5
    @3
    @15
    @36
    wss
    #
    @28
    @8
    @3
    @17
    @38
    @24
    @17
    @15
    cA
    @36
    cin
    @36
    cA
    @36
    @1
    cvv
    cM
    @1
    eqid
    #
    @36
    eqid
    #
    ressbas
    cA
    @36
    inss2
    syl6eqssr
    syl
    ad2antrr
    #
    @25
    @26
    @27
    @3
    @8
    simplr1
    sseldd
    @30
    @15
    @36
    @6
    @41
    @25
    @26
    @27
    @3
    @8
    simplr2
    sseldd
    @30
    @15
    @36
    @9
    @41
    @25
    @26
    @27
    @3
    @8
    simplr3
    sseldd
    @29
    @37
    @8
    @29
    @34
    @7
    @5
    @6
    @3
    @34
    @7
    wceq
    #
    @28
    @3
    @17
    @42
    @24
    cA
    cM
    @34
    cvv
    @1
    @39
    @34
    eqid
    #
    ressle
    #
    syl
    adantr
    breqd
    biimpar
    @36
    @31
    @34
    cM
    @5
    @6
    @9
    @40
    @43
    @31
    eqid
    #
    omndadd
    syl131anc
    @29
    @35
    @13
    wb
    @8
    @29
    @32
    @11
    @33
    @12
    @34
    @7
    @29
    @31
    @10
    @5
    @9
    @29
    @17
    @31
    @10
    wceq
    @3
    @17
    @28
    @24
    adantr
    #
    cA
    @31
    cM
    @1
    cvv
    @39
    @45
    ressplusg
    syl
    #
    oveqd
    @29
    @17
    @42
    @46
    @44
    syl
    @29
    @31
    @10
    @6
    @9
    @47
    oveqd
    breq123d
    adantr
    mpbid
    ex
    ralrimivvva
    @15
    @10
    @7
    @1
    va
    vb
    vc
    @23
    @10
    eqid
    @7
    eqid
    isomnd
    syl3anbrc
end
