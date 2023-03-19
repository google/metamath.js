include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cssc.mm"
include "wbr.mm"
include "wa.mm"
include "chomf.mm"
include "id.mm"
include "eqid.mm"
include "subcssc.mm"
include "cbs.mm"
include "cdm.mm"
include "ccat.mm"
include "subcrcl.mm"
include "eqidd.mm"
include "subcfn.mm"
include "subcss1.mm"
include "reschomf.mm"
include "breq2d.mm"
include "syl5ibr.mm"
include "pm4.71rd.mm"
include "cv.mm"
include "ccid.mm"
include "co.mm"
include "wral.mm"
include "cresc.mm"
include "w3a.mm"
include "simpr.mm"
include "simpl.mm"
include "ssctr.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "2thd.mm"
include "adantr.mm"
include "cxp.mm"
include "wfn.mm"
include "sscfn1.mm"
include "ssc1.mm"
include "sselda.mm"
include "subcid.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "oveq1i.mm"
include "cvv.mm"
include "dmexg.mm"
include "syl.mm"
include "rescabs.mm"
include "syl5req.mm"
include "3anbi123d.mm"
include "issubc3.mm"
include "subccat.mm"
include "3bitr4rd.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "ancom.mm"
include "syl6bb.mm"

theorem subsubc
  let cC: class C
  let cD: class D
  let cH: class H
  let cJ: class J
  let vx: setvar x
  assume subsubc.d: |- D = ( C |`cat H )


  assert |- ( H e. ( Subcat ` C ) -> ( J e. ( Subcat ` D ) <-> ( J e. ( Subcat ` C ) /\ J C_cat H ) ) )

  proof
    cH
    cC
    csubc
    cfv
    #
    wcel
    #
    cJ
    cD
    csubc
    cfv
    wcel
    #
    cJ
    cH
    cssc
    wbr
    #
    cJ
    @0
    wcel
    #
    wa
    #
    @4
    @3
    wa
    @1
    @2
    @3
    @2
    wa
    @5
    @1
    @2
    @3
    @2
    @3
    @1
    cJ
    cD
    chomf
    cfv
    #
    cssc
    wbr
    #
    @2
    cD
    @6
    cJ
    @2
    id
    @6
    eqid
    #
    subcssc
    @1
    cH
    @6
    cJ
    cssc
    @1
    cC
    cbs
    cfv
    #
    cC
    cD
    cH
    cdm
    #
    cdm
    #
    cH
    ccat
    subsubc.d
    @9
    eqid
    #
    cC
    cH
    subcrcl
    #
    @1
    cC
    @11
    cH
    @1
    id
    #
    @1
    @11
    eqidd
    subcfn
    #
    @1
    @9
    cC
    @11
    cH
    @14
    @15
    @12
    subcss1
    reschomf
    breq2d
    #
    syl5ibr
    pm4.71rd
    @1
    @3
    @2
    @4
    @1
    @3
    wa
    #
    cJ
    cC
    chomf
    cfv
    #
    cssc
    wbr
    #
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    #
    @20
    @20
    cJ
    co
    #
    wcel
    #
    vx
    cJ
    cdm
    cdm
    #
    wral
    #
    cC
    cJ
    cresc
    co
    #
    ccat
    wcel
    #
    w3a
    @7
    @20
    cD
    ccid
    cfv
    #
    cfv
    #
    @23
    wcel
    #
    vx
    @25
    wral
    #
    cD
    cJ
    cresc
    co
    #
    ccat
    wcel
    #
    w3a
    @4
    @2
    @17
    @19
    @7
    @26
    @32
    @28
    @34
    @17
    @19
    @7
    @17
    @3
    cH
    @18
    cssc
    wbr
    @19
    @1
    @3
    simpr
    #
    @17
    cC
    @18
    cH
    @1
    @3
    simpl
    #
    @18
    eqid
    #
    subcssc
    cJ
    cH
    @18
    ssctr
    syl2anc
    @1
    @3
    @7
    @16
    biimpa
    2thd
    @17
    @24
    @31
    vx
    @25
    @17
    @20
    @25
    wcel
    #
    wa
    #
    @22
    @30
    @23
    @39
    cC
    cD
    @11
    @21
    cH
    @20
    subsubc.d
    @17
    @1
    @38
    @36
    adantr
    @17
    cH
    @11
    @11
    cxp
    wfn
    #
    @38
    @1
    @40
    @3
    @15
    adantr
    #
    adantr
    @21
    eqid
    #
    @17
    @25
    @11
    @20
    @17
    @25
    @11
    cJ
    cH
    @17
    @25
    cJ
    cH
    @35
    @17
    @25
    eqidd
    sscfn1
    #
    @41
    @35
    ssc1
    #
    sselda
    subcid
    eleq1d
    ralbidva
    @17
    @27
    @33
    ccat
    @17
    @33
    cC
    cH
    cresc
    co
    #
    cJ
    cresc
    co
    @27
    cD
    @45
    cJ
    cresc
    subsubc.d
    oveq1i
    @17
    cC
    @11
    @25
    cH
    cJ
    ccat
    cvv
    @1
    cC
    ccat
    wcel
    @3
    @13
    adantr
    #
    @41
    @43
    @1
    @11
    cvv
    wcel
    #
    @3
    @1
    @10
    cvv
    wcel
    @47
    cH
    @0
    dmexg
    @10
    cvv
    dmexg
    syl
    adantr
    @44
    rescabs
    syl5req
    eleq1d
    3anbi123d
    @17
    vx
    cC
    @27
    @25
    @21
    @18
    cJ
    @37
    @42
    @27
    eqid
    @46
    @43
    issubc3
    @17
    vx
    cD
    @33
    @25
    @29
    @6
    cJ
    @8
    @29
    eqid
    @33
    eqid
    @1
    cD
    ccat
    wcel
    @3
    @1
    cC
    cD
    cH
    subsubc.d
    @14
    subccat
    adantr
    @43
    issubc3
    3bitr4rd
    pm5.32da
    bitrd
    @3
    @4
    ancom
    syl6bb
end
