include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "clp.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cnei.mm"
include "wral.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "crp.mm"
include "ctop.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "a1i.mm"
include "unicntop.mm"
include "islp2.mm"
include "syl3anc.mm"
include "wa.mm"
include "wex.mm"
include "ccom.mm"
include "cbl.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "adantr.mm"
include "simpr.mm"
include "cnfldtopn.mm"
include "blnei.mm"
include "adantlr.mm"
include "simplr.mm"
include "wceq.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "n0.mm"
include "sylib.mm"
include "wi.mm"
include "elinel2.mm"
include "adantl.mm"
include "eldifad.mm"
include "sseldd.mm"
include "abssubd.mm"
include "cnmetdval.mm"
include "eqtr4d.mm"
include "elinel1.mm"
include "cxr.mm"
include "rpxr.mm"
include "ad2antlr.mm"
include "elbl.mm"
include "mpbid.mm"
include "simprd.mm"
include "eqbrtrd.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "neibl.mm"
include "simplbda.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2.mm"
include "rspa.mm"
include "adantll.mm"
include "3adant3.mm"
include "simp3.mm"
include "biimpi.mm"
include "nfre1.mm"
include "eldifi.mm"
include "adantrr.mm"
include "eqtrd.mm"
include "simprr.mm"
include "mpbird.mm"
include "simprl.mm"
include "elind.mm"
include "eximd.mm"
include "syl21anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "impbida.mm"
include "bitrd.mm"

theorem islpcn
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let ve: setvar e
  let vn: setvar n
  assume islpcn.s: |- ( ph -> S C_ CC )
  assume islpcn.p: |- ( ph -> P e. CC )

  disjoint P e
  disjoint P x
  disjoint e x
  disjoint S e
  disjoint S x
  disjoint e ph
  disjoint ph x
  disjoint P n
  disjoint e n
  disjoint n x
  disjoint S n
  disjoint n ph
  assert |- ( ph -> ( P e. ( ( limPt ` ( TopOpen ` CCfld ) ) ` S ) <-> A. e e. RR+ E. x e. ( S \ { P } ) ( abs ` ( x - P ) ) < e ) )

  proof
    wph
    cP
    cS
    ccnfld
    ctopn
    cfv
    #
    clp
    cfv
    cfv
    wcel
    #
    vn
    cv
    #
    cS
    cP
    csn
    #
    cdif
    #
    cin
    #
    c0
    wne
    #
    vn
    @3
    @0
    cnei
    cfv
    cfv
    #
    wral
    #
    vx
    cv
    #
    cP
    cmin
    co
    cabs
    cfv
    #
    ve
    cv
    #
    clt
    wbr
    #
    vx
    @4
    wrex
    #
    ve
    crp
    wral
    #
    wph
    @0
    ctop
    wcel
    #
    cS
    cc
    wss
    #
    cP
    cc
    wcel
    #
    @1
    @8
    wb
    @15
    wph
    @0
    @0
    eqid
    #
    cnfldtop
    a1i
    islpcn.s
    islpcn.p
    cP
    cS
    vn
    @0
    cc
    unicntop
    islp2
    syl3anc
    wph
    @8
    @14
    wph
    @8
    wa
    #
    @13
    ve
    crp
    @19
    @11
    crp
    wcel
    #
    wa
    #
    @9
    @4
    wcel
    #
    @12
    wa
    #
    vx
    wex
    #
    @13
    @21
    @9
    cP
    @11
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    @4
    cin
    #
    wcel
    #
    vx
    wex
    #
    @24
    @21
    @27
    c0
    wne
    #
    @29
    @21
    @26
    @7
    wcel
    #
    @8
    @30
    wph
    @20
    @31
    @8
    wph
    @20
    wa
    #
    @25
    cc
    cxmt
    cfv
    wcel
    #
    @17
    @20
    @31
    @33
    @32
    cnxmet
    a1i
    wph
    @17
    @20
    islpcn.p
    adantr
    #
    wph
    @20
    simpr
    @25
    cP
    @11
    @0
    cc
    @0
    @18
    cnfldtopn
    #
    blnei
    syl3anc
    adantlr
    wph
    @8
    @20
    simplr
    @6
    @30
    vn
    @26
    @7
    @2
    @26
    wceq
    @5
    @27
    c0
    @2
    @26
    @4
    ineq1
    neeq1d
    rspcva
    syl2anc
    vx
    @27
    n0
    sylib
    @21
    @28
    @23
    vx
    wph
    @20
    @28
    @23
    wi
    @8
    @32
    @28
    @23
    @32
    @28
    wa
    #
    @22
    @12
    @28
    @22
    @32
    @9
    @26
    @4
    elinel2
    #
    adantl
    @36
    @10
    cP
    @9
    @25
    co
    #
    @11
    clt
    wph
    @28
    @10
    @38
    wceq
    @20
    wph
    @28
    wa
    #
    @10
    cP
    @9
    cmin
    co
    cabs
    cfv
    #
    @38
    @39
    @9
    cP
    @39
    cS
    cc
    @9
    wph
    @16
    @28
    islpcn.s
    adantr
    @28
    @9
    cS
    wcel
    #
    wph
    @28
    @9
    cS
    @3
    @37
    eldifad
    adantl
    sseldd
    #
    wph
    @17
    @28
    islpcn.p
    adantr
    #
    abssubd
    @39
    @17
    @9
    cc
    wcel
    #
    @38
    @40
    wceq
    #
    @43
    @42
    cP
    @9
    @25
    @25
    eqid
    cnmetdval
    #
    syl2anc
    eqtr4d
    adantlr
    @36
    @44
    @38
    @11
    clt
    wbr
    #
    @36
    @9
    @26
    wcel
    #
    @44
    @47
    wa
    #
    @28
    @48
    @32
    @9
    @26
    @4
    elinel1
    adantl
    @36
    @33
    @17
    @11
    cxr
    wcel
    #
    @48
    @49
    wb
    #
    @33
    @36
    cnxmet
    a1i
    @32
    @17
    @28
    @34
    adantr
    @20
    @50
    wph
    @28
    @11
    rpxr
    #
    ad2antlr
    @9
    @25
    cP
    @11
    cc
    elbl
    #
    syl3anc
    mpbid
    simprd
    eqbrtrd
    jca
    ex
    adantlr
    eximdv
    mpd
    @12
    vx
    @4
    df-rex
    #
    sylibr
    ralrimiva
    wph
    @14
    wa
    #
    @6
    vn
    @7
    @55
    @2
    @7
    wcel
    #
    wa
    #
    @26
    @2
    wss
    #
    ve
    crp
    wrex
    #
    @6
    wph
    @56
    @59
    @14
    wph
    @56
    @2
    cc
    wss
    #
    @59
    wph
    @33
    @17
    @56
    @60
    @59
    wa
    wb
    @33
    wph
    cnxmet
    a1i
    islpcn.p
    @25
    cP
    @0
    @2
    cc
    ve
    @35
    neibl
    syl2anc
    simplbda
    adantlr
    @57
    @58
    @6
    ve
    crp
    @55
    @56
    ve
    wph
    @14
    ve
    wph
    ve
    nfv
    @13
    ve
    crp
    nfra1
    nfan
    @56
    ve
    nfv
    nfan
    @6
    ve
    nfv
    @55
    @20
    @58
    @6
    wi
    wi
    @56
    @55
    @20
    @58
    @6
    @55
    @20
    @58
    w3a
    #
    @32
    @13
    @58
    @6
    @61
    wph
    @20
    wph
    @14
    @20
    @58
    simp1l
    @55
    @20
    @58
    simp2
    jca
    @55
    @20
    @13
    @58
    @14
    @20
    @13
    wph
    @13
    ve
    crp
    rspa
    adantll
    3adant3
    @55
    @20
    @58
    simp3
    @32
    @13
    wa
    #
    @58
    wa
    #
    @9
    @5
    wcel
    #
    vx
    wex
    #
    @6
    @63
    @24
    @65
    @13
    @24
    @32
    @58
    @13
    @24
    @54
    biimpi
    ad2antlr
    @63
    @23
    @64
    vx
    @62
    @58
    vx
    @32
    @13
    vx
    @32
    vx
    nfv
    @12
    vx
    @4
    nfre1
    nfan
    @58
    vx
    nfv
    nfan
    @32
    @58
    @23
    @64
    wi
    @13
    @32
    @58
    wa
    #
    @23
    @64
    @66
    @23
    wa
    #
    @2
    @4
    @9
    @67
    @26
    @2
    @9
    @32
    @58
    @23
    simplr
    @32
    @23
    @48
    @58
    @32
    @23
    wa
    #
    @48
    @49
    wph
    @23
    @49
    @20
    wph
    @23
    wa
    #
    @44
    @47
    wph
    @22
    @44
    @12
    wph
    @22
    wa
    #
    cS
    cc
    @9
    wph
    @16
    @22
    islpcn.s
    adantr
    @22
    @41
    wph
    @9
    cS
    @3
    eldifi
    adantl
    sseldd
    #
    adantrr
    @69
    @38
    @10
    @11
    clt
    wph
    @22
    @38
    @10
    wceq
    @12
    @70
    @38
    @40
    @10
    @70
    @17
    @44
    @45
    wph
    @17
    @22
    islpcn.p
    adantr
    #
    @71
    @46
    syl2anc
    @70
    cP
    @9
    @72
    @71
    abssubd
    eqtrd
    adantrr
    wph
    @22
    @12
    simprr
    eqbrtrd
    jca
    adantlr
    @68
    @33
    @17
    @50
    @51
    @33
    @68
    cnxmet
    a1i
    @32
    @17
    @23
    @34
    adantr
    @20
    @50
    wph
    @23
    @52
    ad2antlr
    @53
    syl3anc
    mpbird
    adantlr
    sseldd
    @66
    @22
    @12
    simprl
    elind
    ex
    adantlr
    eximd
    mpd
    vx
    @5
    n0
    sylibr
    syl21anc
    3exp
    adantr
    rexlimd
    mpd
    ralrimiva
    impbida
    bitrd
end
