include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cnt.mm"
include "cfv.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "crest.mm"
include "co.mm"
include "wrex.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "cuni.mm"
include "cvv.mm"
include "topopn.mm"
include "ssexg.mm"
include "ancoms.mm"
include "sylan.mm"
include "resttop.mm"
include "syldan.mm"
include "3adant3.mm"
include "wa.mm"
include "restuni.mm"
include "sseq2d.mm"
include "biimp3a.mm"
include "eqid.mm"
include "ntropn.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "wb.mm"
include "simp1.mm"
include "uniexg.mm"
include "sylan2.mm"
include "elrest.mm"
include "mpbid.mm"
include "wo.mm"
include "wi.mm"
include "eltopss.mm"
include "sseld.mm"
include "adantrr.mm"
include "3ad2antl1.mm"
include "wn.mm"
include "eldif.mm"
include "simplbi2.mm"
include "orrd.mm"
include "syl6.mm"
include "elin.mm"
include "eleq2.mm"
include "elun1.mm"
include "syl6bir.mm"
include "ad2antll.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "elun2.mm"
include "a1i.mm"
include "jaod.mm"
include "ex.mm"
include "mpdd.mm"
include "ssrdv.mm"
include "adantr.mm"
include "unieqi.mm"
include "eqcomi.mm"
include "ntrss2.mm"
include "unss1.mm"
include "syl.mm"
include "sstrd.mm"
include "simpl1.mm"
include "sstr.mm"
include "3adant1.mm"
include "difss.mm"
include "unss.mm"
include "sylanblc.mm"
include "simprl.mm"
include "simprr.mm"
include "ssntr.mm"
include "syl22anc.mm"
include "ssrin.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "expr.mm"
include "com23.mm"
include "impr.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "elrestr.mm"
include "syl3anc.mm"
include "syl6eleqr.mm"
include "elun.mm"
include "orcom.mm"
include "df-or.mm"
include "bitri.mm"
include "anbi1i.mm"
include "elndif.mm"
include "pm2.27.mm"
include "impcom.mm"
include "syl5bi.mm"
include "eqssd.mm"

theorem restntr
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vo: setvar o
  let vx: setvar x
  assume restcls.1: |- X = U. J
  assume restcls.2: |- K = ( J |`t Y )


  assert |- ( ( J e. Top /\ Y C_ X /\ S C_ Y ) -> ( ( int ` K ) ` S ) = ( ( ( int ` J ) ` ( S u. ( X \ Y ) ) ) i^i Y ) )

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
    cnt
    cfv
    #
    cfv
    #
    cS
    cX
    cY
    cdif
    #
    cun
    #
    cJ
    cnt
    cfv
    cfv
    #
    cY
    cin
    #
    @3
    @5
    vo
    cv
    #
    cY
    cin
    #
    wceq
    #
    @5
    @9
    wss
    #
    vo
    cJ
    @3
    @5
    cJ
    cY
    crest
    co
    #
    wcel
    #
    @12
    vo
    cJ
    wrex
    #
    @3
    @5
    cS
    @14
    cnt
    cfv
    #
    cfv
    #
    @14
    cS
    @4
    @17
    cK
    @14
    cnt
    restcls.2
    fveq2i
    fveq1i
    @3
    @14
    ctop
    wcel
    #
    cS
    @14
    cuni
    #
    wss
    #
    @18
    @14
    wcel
    @0
    @1
    @19
    @2
    @0
    @1
    cY
    cvv
    wcel
    #
    @19
    @0
    cX
    cJ
    wcel
    #
    @1
    @22
    cJ
    cX
    restcls.1
    topopn
    @1
    @23
    @22
    cY
    cX
    cJ
    ssexg
    ancoms
    sylan
    #
    cY
    cJ
    cvv
    resttop
    syldan
    3adant3
    #
    @0
    @1
    @2
    @21
    @0
    @1
    wa
    cY
    @20
    cS
    cY
    cJ
    cX
    restcls.1
    restuni
    sseq2d
    biimp3a
    #
    cS
    @14
    @20
    @20
    eqid
    ntropn
    syl2anc
    syl5eqel
    @3
    @0
    @22
    @15
    @16
    wb
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @22
    @2
    @1
    @0
    @22
    @0
    @1
    cX
    cvv
    wcel
    @22
    @0
    cX
    cJ
    cuni
    cvv
    restcls.1
    cJ
    ctop
    uniexg
    syl5eqel
    cY
    cX
    cvv
    ssexg
    sylan2
    ancoms
    3adant3
    vo
    @5
    cY
    cJ
    ctop
    cvv
    elrest
    syl2anc
    mpbid
    @3
    @10
    cJ
    wcel
    #
    @12
    wa
    #
    wa
    #
    @10
    @7
    wss
    #
    @13
    @30
    @10
    @5
    @6
    cun
    #
    @7
    @30
    vx
    @10
    @32
    @30
    vx
    cv
    #
    @10
    wcel
    #
    @33
    cY
    wcel
    #
    @33
    @6
    wcel
    #
    wo
    #
    @33
    @32
    wcel
    #
    @30
    @34
    @33
    cX
    wcel
    #
    @37
    @0
    @1
    @29
    @34
    @39
    wi
    #
    @2
    @0
    @28
    @40
    @12
    @0
    @28
    wa
    @10
    cX
    @33
    @10
    cJ
    cX
    restcls.1
    eltopss
    sseld
    adantrr
    3ad2antl1
    @39
    @35
    @36
    @36
    @39
    @35
    wn
    @33
    cX
    cY
    eldif
    simplbi2
    orrd
    syl6
    @30
    @34
    @37
    @38
    wi
    @30
    @34
    wa
    #
    @35
    @38
    @36
    @30
    @34
    @35
    @38
    @34
    @35
    wa
    @33
    @11
    wcel
    #
    @30
    @38
    @33
    @10
    cY
    elin
    @12
    @42
    @38
    wi
    @3
    @28
    @12
    @42
    @33
    @5
    wcel
    @38
    @5
    @11
    @33
    eleq2
    @33
    @5
    @6
    elun1
    syl6bir
    ad2antll
    syl5bir
    expdimp
    @36
    @38
    wi
    @41
    @33
    @6
    @5
    elun2
    a1i
    jaod
    ex
    mpdd
    ssrdv
    @30
    @5
    cS
    wss
    #
    @32
    @7
    wss
    @30
    cK
    ctop
    wcel
    #
    @21
    @43
    @30
    cK
    @14
    ctop
    restcls.2
    @3
    @19
    @29
    @25
    adantr
    syl5eqel
    @3
    @21
    @29
    @26
    adantr
    cS
    cK
    @20
    cK
    cuni
    @20
    cK
    @14
    restcls.2
    unieqi
    eqcomi
    #
    ntrss2
    syl2anc
    @5
    cS
    @6
    unss1
    syl
    sstrd
    @3
    @28
    @12
    @31
    @13
    wi
    @3
    @28
    wa
    @31
    @12
    @13
    @3
    @28
    @31
    @12
    @13
    wi
    @3
    @28
    @31
    wa
    #
    wa
    #
    @13
    @12
    @11
    @9
    wss
    #
    @47
    @10
    @8
    wss
    #
    @48
    @47
    @0
    @7
    cX
    wss
    #
    @28
    @31
    @49
    @0
    @1
    @2
    @46
    simpl1
    @47
    cS
    cX
    wss
    #
    @6
    cX
    wss
    #
    @50
    @3
    @51
    @46
    @1
    @2
    @51
    @0
    @2
    @1
    @51
    cS
    cY
    cX
    sstr
    ancoms
    3adant1
    #
    adantr
    cX
    cY
    difss
    #
    cS
    @6
    cX
    unss
    #
    sylanblc
    @3
    @28
    @31
    simprl
    @3
    @28
    @31
    simprr
    @7
    cJ
    @10
    cX
    restcls.1
    ssntr
    syl22anc
    @10
    @8
    cY
    ssrin
    syl
    @5
    @11
    @9
    sseq1
    syl5ibrcom
    expr
    com23
    impr
    mpd
    rexlimddv
    @3
    @44
    @21
    @9
    cK
    wcel
    @9
    cS
    wss
    @9
    @5
    wss
    @3
    cK
    @14
    ctop
    restcls.2
    @25
    syl5eqel
    @26
    @3
    @9
    @14
    cK
    @3
    @0
    @22
    @8
    cJ
    wcel
    #
    @9
    @14
    wcel
    @27
    @0
    @1
    @22
    @2
    @24
    3adant3
    @3
    @0
    @50
    @56
    @27
    @3
    @51
    @52
    @50
    @53
    @54
    @55
    sylanblc
    #
    @7
    cJ
    cX
    restcls.1
    ntropn
    syl2anc
    @8
    cY
    cJ
    ctop
    cvv
    elrestr
    syl3anc
    restcls.2
    syl6eleqr
    @3
    @9
    @7
    cY
    cin
    #
    cS
    @3
    @8
    @7
    wss
    #
    @9
    @58
    wss
    @3
    @0
    @50
    @59
    @27
    @57
    @7
    cJ
    cX
    restcls.1
    ntrss2
    syl2anc
    @8
    @7
    cY
    ssrin
    syl
    @3
    vx
    @58
    cS
    @33
    @58
    wcel
    #
    @36
    wn
    #
    @33
    cS
    wcel
    #
    wi
    #
    @35
    wa
    #
    @3
    @62
    @60
    @33
    @7
    wcel
    #
    @35
    wa
    @64
    @33
    @7
    cY
    elin
    @65
    @63
    @35
    @65
    @62
    @36
    wo
    #
    @63
    @33
    cS
    @6
    elun
    @66
    @36
    @62
    wo
    @63
    @62
    @36
    orcom
    @36
    @62
    df-or
    bitri
    bitri
    anbi1i
    bitri
    @64
    @62
    wi
    @3
    @35
    @63
    @62
    @35
    @61
    @63
    @62
    wi
    @33
    cY
    cX
    elndif
    @61
    @62
    pm2.27
    syl
    impcom
    a1i
    syl5bi
    ssrdv
    sstrd
    cS
    cK
    @9
    @20
    @45
    ssntr
    syl22anc
    eqssd
end
