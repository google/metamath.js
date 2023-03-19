include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "ccl.mm"
include "cfv.mm"
include "cin.mm"
include "ccld.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "sstr.mm"
include "ancoms.mm"
include "3adant1.mm"
include "clscld.mm"
include "syl2anc.mm"
include "eqid.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "crest.mm"
include "co.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "wb.mm"
include "restcld.mm"
include "3adant3.mm"
include "syl5bb.mm"
include "mpbird.mm"
include "sscls.mm"
include "simp3.mm"
include "ssind.mm"
include "cuni.mm"
include "clsss2.mm"
include "fveq1i.mm"
include "cvv.mm"
include "id.mm"
include "topopn.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "resttop.mm"
include "syldan.mm"
include "restuni.mm"
include "sseqtrd.mm"
include "syl5eqel.mm"
include "mpbid.mm"
include "wa.mm"
include "unieqi.mm"
include "eqcomi.mm"
include "adantr.mm"
include "inss1.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "ad2antll.mm"
include "sstrd.mm"
include "wi.mm"
include "adantl.mm"
include "ssrin.mm"
include "syl.mm"
include "sseq2.mm"
include "syl5ibrcom.mm"
include "expr.mm"
include "com23.mm"
include "impr.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "eqssd.mm"

theorem restcls
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vo: setvar o
  let vx: setvar x
  assume restcls.1: |- X = U. J
  assume restcls.2: |- K = ( J |`t Y )


  assert |- ( ( J e. Top /\ Y C_ X /\ S C_ Y ) -> ( ( cls ` K ) ` S ) = ( ( ( cls ` J ) ` S ) i^i Y ) )

  proof
    cJ
    ctop
    wcel
    #
    cY
    cX
    wss
    #
    cS
    cY
    wss
    #
    w3a
    #
    cS
    cK
    ccl
    cfv
    #
    cfv
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cY
    cin
    #
    @3
    @7
    cK
    ccld
    cfv
    #
    wcel
    #
    cS
    @7
    wss
    @5
    @7
    wss
    @3
    @9
    @7
    vx
    cv
    #
    cY
    cin
    #
    wceq
    #
    vx
    cJ
    ccld
    cfv
    #
    wrex
    #
    @3
    @6
    @13
    wcel
    #
    @7
    @7
    wceq
    #
    @14
    @3
    @0
    cS
    cX
    wss
    #
    @15
    @0
    @1
    @2
    simp1
    #
    @1
    @2
    @17
    @0
    @2
    @1
    @17
    cS
    cY
    cX
    sstr
    ancoms
    3adant1
    #
    cS
    cJ
    cX
    restcls.1
    clscld
    syl2anc
    @7
    eqid
    @12
    @16
    vx
    @6
    @13
    @10
    @6
    wceq
    @11
    @7
    @7
    @10
    @6
    cY
    ineq1
    eqeq2d
    rspcev
    sylancl
    @9
    @7
    cJ
    cY
    crest
    co
    #
    ccld
    cfv
    #
    wcel
    #
    @3
    @14
    @8
    @21
    @7
    cK
    @20
    ccld
    restcls.2
    fveq2i
    eleq2i
    @0
    @1
    @22
    @14
    wb
    @2
    vx
    @7
    cY
    cJ
    cX
    restcls.1
    restcld
    3adant3
    syl5bb
    mpbird
    @3
    cS
    @6
    cY
    @3
    @0
    @17
    cS
    @6
    wss
    @18
    @19
    cS
    cJ
    cX
    restcls.1
    sscls
    syl2anc
    @0
    @1
    @2
    simp3
    #
    ssind
    @7
    cS
    cK
    cK
    cuni
    #
    @24
    eqid
    clsss2
    syl2anc
    @3
    @5
    @11
    wceq
    #
    @7
    @5
    wss
    #
    vx
    @13
    @3
    @5
    @21
    wcel
    #
    @25
    vx
    @13
    wrex
    #
    @3
    @5
    cS
    @20
    ccl
    cfv
    #
    cfv
    #
    @21
    cS
    @4
    @29
    cK
    @20
    ccl
    restcls.2
    fveq2i
    fveq1i
    @3
    @20
    ctop
    wcel
    #
    cS
    @20
    cuni
    #
    wss
    #
    @30
    @21
    wcel
    @0
    @1
    @31
    @2
    @0
    @1
    cY
    cvv
    wcel
    #
    @31
    @1
    @1
    cX
    cJ
    wcel
    @34
    @0
    @1
    id
    cJ
    cX
    restcls.1
    topopn
    cY
    cX
    cJ
    ssexg
    syl2anr
    cY
    cJ
    cvv
    resttop
    syldan
    #
    3adant3
    @3
    cS
    cY
    @32
    @23
    @0
    @1
    cY
    @32
    wceq
    @2
    cY
    cJ
    cX
    restcls.1
    restuni
    3adant3
    sseqtrd
    #
    cS
    @20
    @32
    @32
    eqid
    clscld
    syl2anc
    syl5eqel
    @0
    @1
    @27
    @28
    wb
    @2
    vx
    @5
    cY
    cJ
    cX
    restcls.1
    restcld
    3adant3
    mpbid
    @3
    @10
    @13
    wcel
    #
    @25
    wa
    #
    wa
    #
    cS
    @10
    wss
    #
    @26
    @39
    cS
    @5
    @10
    @3
    cS
    @5
    wss
    #
    @38
    @3
    cK
    ctop
    wcel
    #
    @33
    @41
    @0
    @1
    @42
    @2
    @0
    @1
    wa
    cK
    @20
    ctop
    restcls.2
    @35
    syl5eqel
    3adant3
    @36
    cS
    cK
    @32
    @24
    @32
    cK
    @20
    restcls.2
    unieqi
    eqcomi
    sscls
    syl2anc
    adantr
    @25
    @5
    @10
    wss
    #
    @3
    @37
    @25
    @43
    @11
    @10
    wss
    @10
    cY
    inss1
    @5
    @11
    @10
    sseq1
    mpbiri
    ad2antll
    sstrd
    @3
    @37
    @25
    @40
    @26
    wi
    @3
    @37
    wa
    @40
    @25
    @26
    @3
    @37
    @40
    @25
    @26
    wi
    @3
    @37
    @40
    wa
    #
    wa
    #
    @26
    @25
    @7
    @11
    wss
    #
    @45
    @6
    @10
    wss
    #
    @46
    @44
    @47
    @3
    @10
    cS
    cJ
    cX
    restcls.1
    clsss2
    adantl
    @6
    @10
    cY
    ssrin
    syl
    @5
    @11
    @7
    sseq2
    syl5ibrcom
    expr
    com23
    impr
    mpd
    rexlimddv
    eqssd
end
