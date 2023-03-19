include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cxne.mm"
include "wcel.mm"
include "crab.mm"
include "cinf.mm"
include "cpnf.mm"
include "wceq.mm"
include "wa.mm"
include "cmnf.mm"
include "xnegmnf.mm"
include "eqcomi.mm"
include "a1i.mm"
include "wss.mm"
include "supxrpnf.mm"
include "sylan.mm"
include "ssrab2.mm"
include "xnegeq.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "mnfxr.mm"
include "id.mm"
include "elrabd.mm"
include "infxrmnf.mm"
include "syl2anc.mm"
include "adantl.mm"
include "xnegeqd.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "cneg.mm"
include "cr.mm"
include "ssdifssd.mm"
include "adantr.mm"
include "difssd.mm"
include "ssnel.mm"
include "neldifsnd.mm"
include "xrssre.mm"
include "supminfxr.mm"
include "supxrmnf2.mm"
include "syl.mm"
include "eqcomd.mm"
include "wi.mm"
include "wral.mm"
include "rexr.mm"
include "simpl.mm"
include "rexnegd.mm"
include "eldifi.mm"
include "eqeltrd.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "wne.mm"
include "renepnf.mm"
include "elsni.mm"
include "necon3ai.mm"
include "eldifd.mm"
include "ex.mm"
include "rgen.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfdif.mm"
include "rabssf.mm"
include "nfv.mm"
include "sseldi.mm"
include "simprbi.mm"
include "biimpac.mm"
include "adantll.mm"
include "simpll.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "sylan2.mm"
include "eldifsni.mm"
include "xrred.mm"
include "ssdf2.mm"
include "eqtr2d.mm"
include "xnegneg.mm"
include "neneqd.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "ssrabf.mm"
include "eqssd.mm"
include "infeq1d.mm"
include "infxrpnf2.mm"
include "ax-mp.mm"
include "pm2.61dan.mm"
include "cbvrabv.mm"
include "infeq1i.mm"
include "xnegeqi.mm"

theorem supminfxr2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume supminfxr2.1: |- ( ph -> A C_ RR* )

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ph -> sup ( A , RR* , < ) = -e inf ( { x e. RR* | -e x e. A } , RR* , < ) )

  proof
    wph
    cA
    cxr
    clt
    csup
    #
    vy
    cv
    #
    cxne
    #
    cA
    wcel
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cxne
    #
    vx
    cv
    #
    cxne
    #
    cA
    wcel
    #
    vx
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cxne
    #
    wph
    cpnf
    cA
    wcel
    #
    @0
    @6
    wceq
    wph
    @13
    wa
    #
    cpnf
    cmnf
    cxne
    #
    @0
    @6
    cpnf
    @15
    wceq
    @14
    @15
    cpnf
    xnegmnf
    eqcomi
    a1i
    wph
    cA
    cxr
    wss
    #
    @13
    @0
    cpnf
    wceq
    supminfxr2.1
    cA
    supxrpnf
    sylan
    @14
    @5
    cmnf
    @13
    @5
    cmnf
    wceq
    #
    wph
    @13
    @4
    cxr
    wss
    #
    cmnf
    @4
    wcel
    @17
    @18
    @13
    @3
    vy
    cxr
    ssrab2
    #
    a1i
    @13
    @3
    @13
    vy
    cmnf
    cxr
    @1
    cmnf
    wceq
    #
    @2
    cpnf
    cA
    @20
    @2
    @15
    cpnf
    @1
    cmnf
    xnegeq
    @15
    cpnf
    wceq
    #
    @20
    xnegmnf
    a1i
    eqtrd
    eleq1d
    #
    cmnf
    cxr
    wcel
    @13
    mnfxr
    a1i
    @13
    id
    elrabd
    @4
    infxrmnf
    syl2anc
    adantl
    xnegeqd
    3eqtr4d
    wph
    @13
    wn
    #
    wa
    #
    cA
    cmnf
    csn
    #
    cdif
    #
    cxr
    clt
    csup
    #
    @1
    cneg
    #
    @26
    wcel
    #
    vy
    cr
    crab
    #
    cxr
    clt
    cinf
    #
    cxne
    #
    @0
    @6
    @24
    vy
    @26
    @24
    @26
    wph
    @26
    cxr
    wss
    @23
    wph
    cA
    cxr
    @25
    supminfxr2.1
    ssdifssd
    adantr
    @23
    cpnf
    @26
    wcel
    wn
    #
    wph
    @23
    @26
    cA
    wss
    @23
    @33
    @23
    cA
    @25
    difssd
    @23
    id
    @26
    cA
    cpnf
    ssnel
    syl2anc
    adantl
    @24
    cmnf
    cA
    neldifsnd
    xrssre
    supminfxr
    wph
    @0
    @27
    wceq
    @23
    wph
    @27
    @0
    wph
    @16
    @27
    @0
    wceq
    supminfxr2.1
    cA
    supxrmnf2
    syl
    eqcomd
    adantr
    @23
    @6
    @32
    wceq
    wph
    @23
    @5
    @31
    @23
    @31
    @4
    cpnf
    csn
    #
    cdif
    #
    cxr
    clt
    cinf
    #
    @5
    @23
    cxr
    @30
    @35
    clt
    @23
    @30
    @35
    @23
    @29
    @1
    @35
    wcel
    #
    wi
    #
    vy
    cr
    wral
    #
    @30
    @35
    wss
    @39
    @23
    @38
    vy
    cr
    @1
    cr
    wcel
    #
    @29
    @37
    @40
    @29
    wa
    #
    @1
    @4
    @34
    @41
    @1
    cxr
    wcel
    #
    @3
    wa
    @1
    @4
    wcel
    #
    @41
    @42
    @3
    @40
    @42
    @29
    @1
    rexr
    adantr
    @41
    @2
    @28
    cA
    @41
    @1
    @40
    @29
    simpl
    #
    rexnegd
    @29
    @28
    cA
    wcel
    @40
    @28
    cA
    @25
    eldifi
    adantl
    eqeltrd
    jca
    @3
    vy
    cxr
    rabid
    #
    sylibr
    @41
    @40
    @1
    @34
    wcel
    #
    wn
    #
    @44
    @40
    @1
    cpnf
    wne
    #
    @47
    @1
    renepnf
    @46
    @1
    cpnf
    @1
    cpnf
    elsni
    necon3ai
    syl
    syl
    eldifd
    ex
    rgen
    a1i
    @29
    vy
    cr
    @35
    vy
    @4
    @34
    @3
    vy
    cxr
    nfrab1
    vy
    @34
    nfcv
    nfdif
    #
    rabssf
    sylibr
    @23
    @35
    cr
    wss
    #
    @29
    vy
    @35
    wral
    #
    wa
    @35
    @30
    wss
    @23
    @50
    @51
    @23
    vy
    @35
    cr
    @23
    vy
    nfv
    @49
    vy
    cr
    nfcv
    #
    @23
    @37
    wa
    #
    @1
    @37
    @42
    @23
    @37
    @4
    cxr
    @1
    @19
    @1
    @4
    @34
    eldifi
    #
    sseldi
    #
    adantl
    @37
    @23
    @3
    @1
    cmnf
    wne
    @37
    @43
    @3
    @54
    @43
    @42
    @3
    @45
    simprbi
    syl
    #
    @23
    @3
    wa
    #
    @1
    cmnf
    @57
    @20
    @13
    @3
    @20
    @13
    @23
    @20
    @3
    @13
    @22
    biimpac
    adantll
    @23
    @3
    @20
    simpll
    pm2.65da
    neqned
    sylan2
    @37
    @48
    @23
    @1
    @4
    cpnf
    eldifsni
    #
    adantl
    xrred
    #
    ssdf2
    @23
    @29
    vy
    @35
    @53
    @2
    @28
    @26
    @53
    @1
    @59
    rexnegd
    @53
    @2
    cA
    @25
    @37
    @3
    @23
    @56
    adantl
    @37
    @2
    @25
    wcel
    #
    wn
    @23
    @37
    @60
    @1
    cpnf
    wceq
    #
    @37
    @60
    wa
    @42
    @2
    cmnf
    wceq
    #
    @61
    @37
    @42
    @60
    @55
    adantr
    @60
    @62
    @37
    @2
    cmnf
    elsni
    adantl
    @42
    @62
    wa
    cpnf
    @2
    cxne
    #
    @1
    @62
    cpnf
    @63
    wceq
    @42
    @62
    @63
    @15
    cpnf
    @2
    cmnf
    xnegeq
    @21
    @62
    xnegmnf
    a1i
    eqtr2d
    adantl
    @42
    @63
    @1
    wceq
    @62
    @1
    xnegneg
    adantr
    eqtr2d
    syl2anc
    @37
    @61
    wn
    @60
    @37
    @1
    cpnf
    @58
    neneqd
    adantr
    pm2.65da
    adantl
    eldifd
    eqeltrrd
    ralrimiva
    jca
    @29
    vy
    cr
    @35
    @49
    @52
    ssrabf
    sylibr
    eqssd
    infeq1d
    @36
    @5
    wceq
    #
    @23
    @18
    @64
    @19
    @4
    infxrpnf2
    ax-mp
    a1i
    eqtr2d
    xnegeqd
    adantl
    3eqtr4d
    pm2.61dan
    @6
    @12
    wceq
    wph
    @5
    @11
    cxr
    @4
    @10
    clt
    @3
    @9
    vy
    vx
    cxr
    @1
    @7
    wceq
    @2
    @8
    cA
    @1
    @7
    xnegeq
    eleq1d
    cbvrabv
    infeq1i
    xnegeqi
    a1i
    eqtrd
end
