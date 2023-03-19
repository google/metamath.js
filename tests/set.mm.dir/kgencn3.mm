include "ckgen.mm"
include "crn.mm"
include "wcel.mm"
include "ctop.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "eqid.mm"
include "cnf.mm"
include "adantl.mm"
include "wss.mm"
include "crest.mm"
include "ccmp.mm"
include "cin.mm"
include "wi.mm"
include "cpw.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "syl5sseq.mm"
include "cres.mm"
include "cnvresima.mm"
include "wfun.mm"
include "ad2antrr.mm"
include "ffun.mm"
include "inpreima.mm"
include "3syl.mm"
include "ineq1d.mm"
include "in32.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "dminss.mm"
include "sstri.mm"
include "a1i.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "simpr.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "cnrest.mm"
include "syl2anc.mm"
include "ctopon.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "toptopon.mm"
include "df-ima.mm"
include "eqimss2i.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simplr.mm"
include "simprr.mm"
include "imacmp.mm"
include "kgeni.mm"
include "cnima.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "kgentop.mm"
include "elkgen.mm"
include "mpbir2and.mm"
include "kgenidm.mm"
include "eleqtrd.mm"
include "kgentopon.mm"
include "sylbi.mm"
include "iscn.mm"
include "syl2an.mm"
include "ex.mm"
include "ssrdv.mm"
include "toponcom.mm"
include "kgenss.mm"
include "cnss2.mm"
include "eqssd.mm"

theorem kgencn3
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. ran kGen /\ K e. Top ) -> ( J Cn K ) = ( J Cn ( kGen ` K ) ) )

  proof
    cJ
    ckgen
    crn
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cJ
    cK
    ccn
    co
    #
    cJ
    cK
    ckgen
    cfv
    #
    ccn
    co
    #
    @2
    vf
    @3
    @5
    @2
    vf
    cv
    #
    @3
    wcel
    #
    @6
    @5
    wcel
    #
    @2
    @7
    wa
    #
    @8
    cJ
    cuni
    #
    cK
    cuni
    #
    @6
    wf
    #
    @6
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    @4
    wral
    #
    @7
    @12
    @2
    @6
    cJ
    cK
    @10
    @11
    @10
    eqid
    #
    @11
    eqid
    #
    cnf
    adantl
    #
    @9
    @16
    vx
    @4
    @9
    @14
    @4
    wcel
    #
    wa
    #
    @15
    cJ
    ckgen
    cfv
    #
    cJ
    @22
    @15
    @23
    wcel
    #
    @15
    @10
    wss
    #
    cJ
    vy
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    @15
    @26
    cin
    #
    @27
    wcel
    #
    wi
    #
    vy
    @10
    cpw
    #
    wral
    #
    @22
    @6
    cdm
    #
    @15
    @10
    @6
    @14
    cnvimass
    #
    @9
    @34
    @10
    wceq
    #
    @21
    @9
    @12
    @36
    @20
    @10
    @11
    @6
    fdm
    syl
    adantr
    syl5sseq
    @22
    @31
    vy
    @32
    @22
    @26
    @32
    wcel
    #
    @28
    @30
    @22
    @37
    @28
    wa
    #
    wa
    #
    @6
    @26
    cres
    #
    ccnv
    @14
    @6
    @26
    cima
    #
    cin
    #
    cima
    #
    @29
    @27
    @39
    @43
    @13
    @42
    cima
    #
    @26
    cin
    #
    @29
    @26
    @42
    @6
    cnvresima
    @39
    @45
    @15
    @13
    @41
    cima
    #
    cin
    #
    @26
    cin
    #
    @29
    @39
    @44
    @47
    @26
    @39
    @12
    @6
    wfun
    @44
    @47
    wceq
    @9
    @12
    @21
    @38
    @20
    ad2antrr
    #
    @10
    @11
    @6
    ffun
    @14
    @41
    @6
    inpreima
    3syl
    ineq1d
    @39
    @48
    @29
    @46
    cin
    #
    @29
    @15
    @46
    @26
    in32
    @39
    @29
    @46
    wss
    #
    @50
    @29
    wceq
    @51
    @39
    @29
    @34
    @26
    cin
    #
    @46
    @15
    @34
    wss
    @29
    @52
    wss
    @35
    @15
    @34
    @26
    ssrin
    ax-mp
    @26
    @6
    dminss
    sstri
    a1i
    @29
    @46
    df-ss
    sylib
    syl5eq
    eqtrd
    syl5eq
    @39
    @40
    @27
    cK
    @41
    crest
    co
    #
    ccn
    co
    wcel
    #
    @42
    @53
    wcel
    #
    @43
    @27
    wcel
    @39
    @40
    @27
    cK
    ccn
    co
    wcel
    #
    @54
    @39
    @7
    @26
    @10
    wss
    #
    @56
    @9
    @7
    @21
    @38
    @2
    @7
    simpr
    ad2antrr
    #
    @37
    @57
    @22
    @28
    @26
    @10
    elpwi
    ad2antrl
    @26
    @6
    cJ
    cK
    @10
    @18
    cnrest
    syl2anc
    @39
    cK
    @11
    ctopon
    cfv
    #
    wcel
    #
    @40
    crn
    #
    @41
    wss
    #
    @41
    @11
    wss
    @56
    @54
    wb
    @39
    @1
    @60
    @2
    @1
    @7
    @21
    @38
    @0
    @1
    simpr
    #
    ad3antrrr
    cK
    @11
    @19
    toptopon
    #
    sylib
    @62
    @39
    @41
    @61
    @6
    @26
    df-ima
    eqimss2i
    a1i
    @39
    @41
    @6
    crn
    #
    @11
    @6
    @26
    imassrn
    @39
    @12
    @65
    @11
    wss
    @49
    @10
    @11
    @6
    frn
    syl
    syl5ss
    @41
    @40
    @27
    cK
    @11
    cnrest2
    syl3anc
    mpbid
    @39
    @21
    @53
    ccmp
    wcel
    #
    @55
    @9
    @21
    @38
    simplr
    @39
    @7
    @28
    @66
    @58
    @22
    @37
    @28
    simprr
    @26
    @6
    cJ
    cK
    imacmp
    syl2anc
    @14
    cK
    @41
    kgeni
    syl2anc
    @42
    @40
    @27
    @53
    cnima
    syl2anc
    eqeltrrd
    expr
    ralrimiva
    @22
    cJ
    @10
    ctopon
    cfv
    wcel
    #
    @24
    @25
    @33
    wa
    wb
    @22
    cJ
    ctop
    wcel
    #
    @67
    @0
    @68
    @1
    @7
    @21
    cJ
    kgentop
    #
    ad3antrrr
    cJ
    @10
    @18
    toptopon
    #
    sylib
    @15
    vy
    cJ
    @10
    elkgen
    syl
    mpbir2and
    @0
    @23
    cJ
    wceq
    @1
    @7
    @21
    cJ
    kgenidm
    ad3antrrr
    eleqtrd
    ralrimiva
    @2
    @8
    @12
    @17
    wa
    wb
    #
    @7
    @0
    @67
    @4
    @59
    wcel
    #
    @71
    @1
    @0
    @68
    @67
    @69
    @70
    sylib
    @1
    @60
    @72
    @64
    cK
    @11
    kgentopon
    sylbi
    #
    vx
    @6
    cJ
    @4
    @10
    @11
    iscn
    syl2an
    adantr
    mpbir2and
    ex
    ssrdv
    @2
    cK
    @4
    cuni
    #
    ctopon
    cfv
    wcel
    #
    cK
    @4
    wss
    #
    @5
    @3
    wss
    @2
    @1
    @72
    @75
    @63
    @1
    @72
    @0
    @73
    adantl
    cK
    @4
    toponcom
    syl2anc
    @1
    @76
    @0
    cK
    kgenss
    adantl
    cJ
    @4
    cK
    @74
    @74
    eqid
    cnss2
    syl2anc
    eqssd
end
