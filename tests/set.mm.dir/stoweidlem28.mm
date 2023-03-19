include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "cle.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "halfre.mm"
include "halfgt0.mm"
include "elrpii.mm"
include "a1i.mm"
include "halflt1.mm"
include "nfcv.mm"
include "nfdif.mm"
include "nfeq1.mm"
include "rzalf.mm"
include "adantl.mm"
include "ovex.mm"
include "eleq1.mm"
include "breq1.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "spcev.mm"
include "syl3anc.mm"
include "wn.mm"
include "cres.mm"
include "simplll.mm"
include "simplr.mm"
include "simpr.mm"
include "cr.mm"
include "wf.mm"
include "ccn.mm"
include "eqid.mm"
include "fcnre.mm"
include "adantr.mm"
include "eldifi.mm"
include "ffvelrnd.mm"
include "cc0.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvralf.mm"
include "biimpi.mm"
include "r19.21bi.mm"
include "sylan.mm"
include "elrpd.mm"
include "3adant3.mm"
include "nfcri.mm"
include "nfra1.mm"
include "nf3an.mm"
include "rspa.mm"
include "3ad2antl3.mm"
include "simpl2.mm"
include "fvres.mm"
include "syl.mm"
include "3brtr3d.mm"
include "ex.mm"
include "ralrimi.mm"
include "wi.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mp2and.mm"
include "simpl1.mm"
include "simprl.mm"
include "simprr.mm"
include "cif.mm"
include "3ad2ant1.mm"
include "difssd.mm"
include "simp2.mm"
include "simp3.mm"
include "stoweidlem5.mm"
include "exlimddv.mm"
include "wrex.mm"
include "crest.mm"
include "cuni.mm"
include "ccmp.mm"
include "ccld.mm"
include "ctop.mm"
include "wss.mm"
include "wb.mm"
include "cmptop.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "isopn2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cmpcld.mm"
include "cnrest.mm"
include "wne.mm"
include "df-ne.mm"
include "restuni.mm"
include "neeq1d.mm"
include "syl5rbbr.mm"
include "biimpar.mm"
include "evth2.mm"
include "nfov.mm"
include "nfuni.mm"
include "nfres.mm"
include "nffv.mm"
include "nfbr.mm"
include "rexbii.mm"
include "sylib.mm"
include "raleqf.mm"
include "rexeqbi1dv.mm"
include "mpbird.mm"
include "r19.29a.mm"
include "pm2.61dan.mm"

theorem stoweidlem28
  let wph: wff ph
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let vd: setvar d
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  let vk: setvar k
  assume stoweidlem28.1: |- F/_ t U
  assume stoweidlem28.2: |- F/ t ph
  assume stoweidlem28.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem28.4: |- T = U. J
  assume stoweidlem28.5: |- ( ph -> J e. Comp )
  assume stoweidlem28.6: |- ( ph -> P e. ( J Cn K ) )
  assume stoweidlem28.7: |- ( ph -> A. t e. ( T \ U ) 0 < ( P ` t ) )
  assume stoweidlem28.8: |- ( ph -> U e. J )

  disjoint d t
  disjoint P d
  disjoint P t
  disjoint T d
  disjoint T t
  disjoint U d
  disjoint J t
  disjoint c d
  disjoint c t
  disjoint c x
  disjoint P c
  disjoint d x
  disjoint t x
  disjoint P x
  disjoint T c
  disjoint T x
  disjoint U c
  disjoint U x
  disjoint c ph
  disjoint ph x
  disjoint s t
  disjoint s x
  disjoint J s
  disjoint J x
  disjoint K s
  disjoint P s
  disjoint T s
  disjoint U s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> E. d ( d e. RR+ /\ d < 1 /\ A. t e. ( T \ U ) d <_ ( P ` t ) ) )

  proof
    wph
    cT
    cU
    cdif
    #
    c0
    wceq
    #
    vd
    cv
    #
    crp
    wcel
    #
    @2
    c1
    clt
    wbr
    #
    @2
    vt
    cv
    #
    cP
    cfv
    #
    cle
    wbr
    #
    vt
    @0
    wral
    #
    w3a
    #
    vd
    wex
    #
    wph
    @1
    wa
    #
    c1
    c2
    cdiv
    co
    #
    crp
    wcel
    #
    @12
    c1
    clt
    wbr
    #
    @12
    @6
    cle
    wbr
    #
    vt
    @0
    wral
    #
    @10
    @13
    @11
    @12
    halfre
    halfgt0
    elrpii
    a1i
    @14
    @11
    halflt1
    a1i
    @1
    @16
    wph
    @15
    vt
    @0
    vt
    @0
    c0
    vt
    cT
    cU
    vt
    cT
    nfcv
    stoweidlem28.1
    nfdif
    #
    nfeq1
    rzalf
    adantl
    @9
    @13
    @14
    @16
    w3a
    vd
    @12
    c1
    c2
    cdiv
    ovex
    @2
    @12
    wceq
    #
    @3
    @13
    @4
    @14
    @8
    @16
    @2
    @12
    crp
    eleq1
    @2
    @12
    c1
    clt
    breq1
    @18
    @7
    @15
    vt
    @0
    @2
    @12
    @6
    cle
    breq1
    ralbidv
    3anbi123d
    spcev
    syl3anc
    wph
    @1
    wn
    #
    wa
    #
    vx
    cv
    #
    cP
    @0
    cres
    #
    cfv
    #
    @5
    @22
    cfv
    #
    cle
    wbr
    #
    vt
    @0
    wral
    #
    @10
    vx
    @0
    @20
    @21
    @0
    wcel
    #
    wa
    #
    @26
    wa
    wph
    @27
    @26
    @10
    wph
    @19
    @27
    @26
    simplll
    @20
    @27
    @26
    simplr
    @28
    @26
    simpr
    wph
    @27
    @26
    w3a
    #
    vc
    cv
    #
    crp
    wcel
    #
    @30
    @6
    cle
    wbr
    #
    vt
    @0
    wral
    #
    wa
    #
    @10
    vc
    @29
    @21
    cP
    cfv
    #
    crp
    wcel
    #
    @35
    @6
    cle
    wbr
    #
    vt
    @0
    wral
    #
    @34
    vc
    wex
    #
    wph
    @27
    @36
    @26
    wph
    @27
    wa
    #
    @35
    @40
    cT
    cr
    @21
    cP
    wph
    cT
    cr
    cP
    wf
    #
    @27
    wph
    cJ
    cK
    ccn
    co
    #
    cT
    cP
    cJ
    cK
    stoweidlem28.3
    stoweidlem28.4
    @42
    eqid
    stoweidlem28.6
    fcnre
    #
    adantr
    @27
    @21
    cT
    wcel
    wph
    @21
    cT
    cU
    eldifi
    adantl
    ffvelrnd
    wph
    cc0
    @6
    clt
    wbr
    #
    vt
    @0
    wral
    #
    @27
    cc0
    @35
    clt
    wbr
    #
    stoweidlem28.7
    @45
    @46
    vx
    @0
    @45
    @46
    vx
    @0
    wral
    @44
    @46
    vt
    vx
    @0
    @17
    vx
    @0
    nfcv
    @44
    vx
    nfv
    @46
    vt
    nfv
    vt
    vx
    weq
    @6
    @35
    cc0
    clt
    @5
    @21
    cP
    fveq2
    breq2d
    cbvralf
    biimpi
    r19.21bi
    sylan
    elrpd
    3adant3
    #
    @29
    @37
    vt
    @0
    wph
    @27
    @26
    vt
    stoweidlem28.2
    vt
    vx
    @0
    @17
    nfcri
    @25
    vt
    @0
    nfra1
    nf3an
    @29
    @5
    @0
    wcel
    #
    @37
    @29
    @48
    wa
    #
    @23
    @24
    @35
    @6
    cle
    @26
    wph
    @48
    @25
    @27
    @25
    vt
    @0
    rspa
    3ad2antl3
    @49
    @27
    @23
    @35
    wceq
    wph
    @27
    @26
    @48
    simpl2
    @21
    @0
    cP
    fvres
    syl
    @48
    @24
    @6
    wceq
    @29
    @5
    @0
    cP
    fvres
    adantl
    3brtr3d
    ex
    ralrimi
    @29
    @36
    @36
    @38
    wa
    #
    @39
    wi
    @47
    @34
    @50
    vc
    @35
    crp
    @30
    @35
    wceq
    #
    @31
    @36
    @33
    @38
    @30
    @35
    crp
    eleq1
    @51
    @32
    @37
    vt
    @0
    @30
    @35
    @6
    cle
    breq1
    ralbidv
    anbi12d
    spcegv
    syl
    mp2and
    @29
    @34
    wa
    wph
    @31
    @33
    @10
    wph
    @27
    @26
    @34
    simpl1
    @29
    @31
    @33
    simprl
    @29
    @31
    @33
    simprr
    wph
    @31
    @33
    w3a
    #
    vt
    @30
    @30
    @12
    cle
    wbr
    @30
    @12
    cif
    #
    cP
    @0
    cT
    vd
    wph
    @31
    @33
    vt
    stoweidlem28.2
    @31
    vt
    nfv
    @32
    vt
    @0
    nfra1
    nf3an
    @53
    eqid
    wph
    @31
    @41
    @33
    @43
    3ad2ant1
    @52
    cT
    cU
    difssd
    wph
    @31
    @33
    simp2
    wph
    @31
    @33
    simp3
    stoweidlem5
    syl3anc
    exlimddv
    syl3anc
    @20
    @26
    vx
    @0
    wrex
    #
    @25
    vt
    cJ
    @0
    crest
    co
    #
    cuni
    #
    wral
    #
    vx
    @56
    wrex
    #
    @20
    @23
    vs
    cv
    #
    @22
    cfv
    #
    cle
    wbr
    #
    vs
    @56
    wral
    #
    vx
    @56
    wrex
    @58
    @20
    vx
    vs
    @22
    @55
    cK
    @56
    @56
    eqid
    stoweidlem28.3
    wph
    @55
    ccmp
    wcel
    #
    @19
    wph
    cJ
    ccmp
    wcel
    #
    @0
    cJ
    ccld
    cfv
    wcel
    #
    @63
    stoweidlem28.5
    wph
    cU
    cJ
    wcel
    #
    @65
    stoweidlem28.8
    wph
    cJ
    ctop
    wcel
    #
    cU
    cT
    wss
    @66
    @65
    wb
    wph
    @64
    @67
    stoweidlem28.5
    cJ
    cmptop
    syl
    #
    wph
    cU
    cJ
    cuni
    #
    cT
    wph
    @66
    cU
    @69
    wss
    stoweidlem28.8
    cU
    cJ
    elssuni
    syl
    stoweidlem28.4
    syl6sseqr
    cU
    cJ
    cT
    stoweidlem28.4
    isopn2
    syl2anc
    mpbid
    @0
    cJ
    cmpcld
    syl2anc
    adantr
    @20
    cP
    @42
    wcel
    #
    @0
    cT
    wss
    #
    @22
    @55
    cK
    ccn
    co
    wcel
    wph
    @70
    @19
    stoweidlem28.6
    adantr
    @20
    cT
    cU
    difssd
    @0
    cP
    cJ
    cK
    cT
    stoweidlem28.4
    cnrest
    syl2anc
    wph
    @56
    c0
    wne
    #
    @19
    @19
    @0
    c0
    wne
    wph
    @72
    @0
    c0
    df-ne
    wph
    @0
    @56
    c0
    wph
    @67
    @71
    @0
    @56
    wceq
    #
    @68
    wph
    cT
    cU
    difssd
    @0
    cJ
    cT
    stoweidlem28.4
    restuni
    syl2anc
    #
    neeq1d
    syl5rbbr
    biimpar
    evth2
    @62
    @57
    vx
    @56
    @61
    @25
    vs
    vt
    @56
    vs
    @56
    nfcv
    vt
    @55
    vt
    cJ
    @0
    crest
    vt
    cJ
    nfcv
    vt
    crest
    nfcv
    @17
    nfov
    nfuni
    #
    vt
    @23
    @60
    cle
    vt
    @21
    @22
    vt
    cP
    @0
    vt
    cP
    nfcv
    @17
    nfres
    #
    vt
    @21
    nfcv
    nffv
    vt
    cle
    nfcv
    vt
    @59
    @22
    @76
    vt
    @59
    nfcv
    nffv
    nfbr
    @25
    vs
    nfv
    vs
    vt
    weq
    @60
    @24
    @23
    cle
    @59
    @5
    @22
    fveq2
    breq2d
    cbvralf
    rexbii
    sylib
    wph
    @54
    @58
    wb
    #
    @19
    wph
    @73
    @77
    @74
    @26
    @57
    vx
    @0
    @56
    @25
    vt
    @0
    @56
    @17
    @75
    raleqf
    rexeqbi1dv
    syl
    adantr
    mpbird
    r19.29a
    pm2.61dan
end
