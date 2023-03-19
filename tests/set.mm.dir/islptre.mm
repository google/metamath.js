include "clp.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cnei.mm"
include "wral.mm"
include "cioo.mm"
include "co.mm"
include "wi.mm"
include "cxr.mm"
include "ctop.mm"
include "cr.mm"
include "wss.mm"
include "wb.mm"
include "crn.mm"
include "ctg.mm"
include "ctopon.mm"
include "retopon.mm"
include "eqeltri.mm"
include "topontopi.mm"
include "a1i.mm"
include "toponunii.mm"
include "islp2.mm"
include "syl3anc.mm"
include "wa.mm"
include "w3a.mm"
include "simp1r.mm"
include "wrex.mm"
include "iooretop.mm"
include "eleqtrri.mm"
include "snssi.mm"
include "adantl.mm"
include "ssid.mm"
include "wceq.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ioossre.mm"
include "jctil.mm"
include "elioore.mm"
include "snssd.mm"
include "isnei.mm"
include "sylancr.mm"
include "mpbird.mm"
include "3adant1.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "rspccva.mm"
include "syl2anc.mm"
include "3exp.mm"
include "ralrimivv.mm"
include "simplbda.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp3l.mm"
include "simpr.mm"
include "adantr.mm"
include "snssg.mm"
include "syl.mm"
include "jca.mm"
include "tg2.mm"
include "cxp.mm"
include "cpw.mm"
include "wf.mm"
include "wfn.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "simpll.mm"
include "eleqtrd.mm"
include "simplr.mm"
include "eqsstr3d.mm"
include "ex.mm"
include "reximdv.mm"
include "mpd.mm"
include "rexlimiva.mm"
include "3syl.mm"
include "simpl3r.mm"
include "sstr.mm"
include "expcom.mm"
include "anim2d.mm"
include "reximdva.mm"
include "rexlimdv.mm"
include "adantlr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfra2.mm"
include "inss1.mm"
include "simp3r.mm"
include "syl5ss.mm"
include "inss2.mm"
include "ssind.mm"
include "simpllr.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "rsp2.mm"
include "syl3c.mm"
include "ssn0.mm"
include "rexlimd.mm"
include "ralrimiva.mm"
include "impbida.mm"
include "bitrd.mm"

theorem islptre
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vv: setvar v
  let vu: setvar u
  assume islptre.1: |- J = ( topGen ` ran (,) )
  assume islptre.2: |- ( ph -> A C_ RR )
  assume islptre.3: |- ( ph -> B e. RR )

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint J a
  disjoint J b
  disjoint a ph
  disjoint b ph
  disjoint A n
  disjoint a n
  disjoint b n
  disjoint B n
  disjoint B v
  disjoint a v
  disjoint b v
  disjoint n v
  disjoint B u
  disjoint a u
  disjoint b u
  disjoint u v
  disjoint J n
  disjoint J v
  disjoint n ph
  disjoint ph v
  assert |- ( ph -> ( B e. ( ( limPt ` J ) ` A ) <-> A. a e. RR* A. b e. RR* ( B e. ( a (,) b ) -> ( ( a (,) b ) i^i ( A \ { B } ) ) =/= (/) ) ) )

  proof
    wph
    cB
    cA
    cJ
    clp
    cfv
    cfv
    wcel
    #
    vn
    cv
    #
    cA
    cB
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
    @2
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    cB
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wcel
    #
    @10
    @3
    cin
    #
    c0
    wne
    #
    wi
    #
    vb
    cxr
    wral
    #
    va
    cxr
    wral
    #
    wph
    cJ
    ctop
    wcel
    #
    cA
    cr
    wss
    cB
    cr
    wcel
    #
    @0
    @7
    wb
    @17
    wph
    cr
    cJ
    cJ
    cioo
    crn
    #
    ctg
    cfv
    #
    cr
    ctopon
    cfv
    islptre.1
    retopon
    eqeltri
    #
    topontopi
    #
    a1i
    islptre.2
    islptre.3
    cB
    cA
    vn
    cJ
    cr
    cr
    cJ
    @21
    toponunii
    #
    islp2
    syl3anc
    wph
    @7
    @16
    wph
    @7
    wa
    #
    @14
    va
    vb
    cxr
    cxr
    @24
    @8
    cxr
    wcel
    #
    @9
    cxr
    wcel
    #
    wa
    #
    @11
    @13
    @24
    @27
    @11
    w3a
    @7
    @10
    @6
    wcel
    #
    @13
    wph
    @7
    @27
    @11
    simp1r
    @27
    @11
    @28
    @24
    @27
    @11
    wa
    #
    @28
    @10
    cr
    wss
    #
    @2
    vv
    cv
    #
    wss
    #
    @31
    @10
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    wa
    #
    @29
    @35
    @30
    @29
    @10
    cJ
    wcel
    #
    @2
    @10
    wss
    #
    @10
    @10
    wss
    #
    @35
    @37
    @29
    @10
    @20
    cJ
    @8
    @9
    iooretop
    islptre.1
    eleqtrri
    a1i
    @11
    @38
    @27
    cB
    @10
    snssi
    adantl
    @39
    @29
    @10
    ssid
    a1i
    @34
    @38
    @39
    wa
    vv
    @10
    cJ
    @31
    @10
    wceq
    @32
    @38
    @33
    @39
    @31
    @10
    @2
    sseq2
    @31
    @10
    @10
    sseq1
    anbi12d
    rspcev
    syl12anc
    @8
    @9
    ioossre
    jctil
    @29
    @17
    @2
    cr
    wss
    #
    @28
    @36
    wb
    @22
    @11
    @40
    @27
    @11
    cB
    cr
    cB
    @8
    @9
    elioore
    snssd
    adantl
    @2
    vv
    cJ
    @10
    cr
    @23
    isnei
    sylancr
    mpbird
    3adant1
    @5
    @13
    vn
    @10
    @6
    @1
    @10
    wceq
    @4
    @12
    c0
    @1
    @10
    @3
    ineq1
    neeq1d
    rspccva
    syl2anc
    3exp
    ralrimivv
    wph
    @16
    wa
    #
    @5
    vn
    @6
    @41
    @1
    @6
    wcel
    #
    wa
    #
    @11
    @10
    @1
    wss
    #
    wa
    #
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    #
    @5
    wph
    @42
    @47
    @16
    wph
    @42
    wa
    @32
    @31
    @1
    wss
    #
    wa
    #
    vv
    cJ
    wrex
    #
    @47
    wph
    @42
    @1
    cr
    wss
    #
    @50
    wph
    @17
    @40
    @42
    @51
    @50
    wa
    wb
    @22
    wph
    cB
    cr
    islptre.3
    snssd
    @2
    vv
    cJ
    @1
    cr
    @23
    isnei
    sylancr
    simplbda
    wph
    @50
    @47
    wi
    @42
    wph
    @49
    @47
    vv
    cJ
    wph
    @31
    cJ
    wcel
    #
    @49
    @47
    wph
    @52
    @49
    w3a
    #
    @11
    @10
    @31
    wss
    #
    wa
    #
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    #
    @47
    @53
    @31
    @20
    wcel
    #
    cB
    @31
    wcel
    #
    wa
    cB
    vu
    cv
    #
    wcel
    #
    @60
    @31
    wss
    #
    wa
    #
    vu
    @19
    wrex
    @57
    @53
    @58
    @59
    @52
    wph
    @58
    @49
    @52
    @58
    cJ
    @20
    @31
    islptre.1
    eleq2i
    biimpi
    3ad2ant2
    @53
    wph
    @32
    @59
    wph
    @52
    @49
    simp1
    wph
    @52
    @32
    @48
    simp3l
    wph
    @32
    wa
    #
    @59
    @32
    wph
    @32
    simpr
    @64
    @18
    @59
    @32
    wb
    wph
    @18
    @32
    islptre.3
    adantr
    cB
    @31
    cr
    snssg
    syl
    mpbird
    syl2anc
    jca
    vu
    @31
    @19
    cB
    tg2
    @63
    @57
    vu
    @19
    @60
    @19
    wcel
    #
    @63
    wa
    #
    @60
    @10
    wceq
    #
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    #
    @57
    @65
    @69
    @63
    @65
    @69
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @70
    wfn
    @65
    @69
    wb
    ioof
    @70
    @71
    cioo
    ffn
    va
    vb
    cxr
    cxr
    @60
    cioo
    ovelrn
    mp2b
    biimpi
    adantr
    @66
    @68
    @56
    va
    cxr
    @66
    @67
    @55
    vb
    cxr
    @63
    @67
    @55
    wi
    @65
    @63
    @67
    @55
    @63
    @67
    wa
    #
    @11
    @54
    @72
    cB
    @60
    @10
    @61
    @62
    @67
    simpll
    @63
    @67
    simpr
    #
    eleqtrd
    @72
    @10
    @60
    @31
    @73
    @61
    @62
    @67
    simplr
    eqsstr3d
    jca
    ex
    adantl
    reximdv
    reximdv
    mpd
    rexlimiva
    3syl
    @53
    @56
    @46
    va
    cxr
    @53
    @25
    wa
    #
    @55
    @45
    vb
    cxr
    @74
    @26
    wa
    #
    @54
    @44
    @11
    @75
    @48
    @54
    @44
    wi
    @74
    @48
    @26
    @32
    @48
    wph
    @52
    @25
    simpl3r
    adantr
    @54
    @48
    @44
    @10
    @31
    @1
    sstr
    expcom
    syl
    anim2d
    reximdva
    reximdva
    mpd
    3exp
    rexlimdv
    adantr
    mpd
    adantlr
    @43
    @46
    @5
    va
    cxr
    @41
    @42
    va
    wph
    @16
    va
    wph
    va
    nfv
    @15
    va
    cxr
    nfra1
    nfan
    @42
    va
    nfv
    nfan
    @5
    va
    nfv
    @43
    @25
    @46
    @5
    wi
    @43
    @25
    wa
    #
    @45
    @5
    vb
    cxr
    @43
    @25
    vb
    @41
    @42
    vb
    wph
    @16
    vb
    wph
    vb
    nfv
    @14
    va
    vb
    cxr
    cxr
    nfra2
    nfan
    @42
    vb
    nfv
    nfan
    @25
    vb
    nfv
    nfan
    @5
    vb
    nfv
    @76
    @26
    @45
    @5
    @76
    @26
    @45
    w3a
    #
    @12
    @4
    wss
    @13
    @5
    @77
    @12
    @1
    @3
    @77
    @12
    @10
    @1
    @10
    @3
    inss1
    @76
    @26
    @11
    @44
    simp3r
    syl5ss
    @12
    @3
    wss
    @77
    @10
    @3
    inss2
    a1i
    ssind
    @77
    @16
    @27
    @11
    @13
    @76
    @26
    @16
    @45
    wph
    @16
    @42
    @25
    simpllr
    3ad2ant1
    @77
    @25
    @26
    @43
    @25
    @26
    @45
    simp1r
    @76
    @26
    @45
    simp2
    jca
    @76
    @26
    @11
    @44
    simp3l
    @14
    va
    vb
    cxr
    cxr
    rsp2
    syl3c
    @12
    @4
    ssn0
    syl2anc
    3exp
    rexlimd
    ex
    rexlimd
    mpd
    ralrimiva
    impbida
    bitrd
end
