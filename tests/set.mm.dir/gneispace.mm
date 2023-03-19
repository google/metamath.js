include "wcel.mm"
include "wfun.mm"
include "crn.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "wa.mm"
include "wel.mm"
include "cv.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wne.mm"
include "w3a.mm"
include "gneispace3.mm"
include "simpll.mm"
include "simplr.mm"
include "difss.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sstri.mm"
include "syl6ss.mm"
include "simpr.mm"
include "simpl.mm"
include "fvelrn.mm"
include "sylan.mm"
include "ssel2.mm"
include "eldifsni.mm"
include "syl.mm"
include "syl2an2r.mm"
include "ralrimiva.mm"
include "r19.26.mm"
include "biimpri.mm"
include "3jca.mm"
include "simp1.mm"
include "cin.mm"
include "wceq.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "wex.mm"
include "19.8a.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "rsp.mm"
include "wn.mm"
include "wal.mm"
include "wrex.mm"
include "df-ex.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "0el.mm"
include "xchbinxr.mm"
include "biimpi.mm"
include "elinel1.mm"
include "nsyl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "disjdif2.mm"
include "syl6.mm"
include "simp2.mm"
include "ex.mm"
include "fvex.mm"
include "elpw.mm"
include "df-ss.mm"
include "sylbb.mm"
include "syl6an.mm"
include "jcad.mm"
include "eqtr.mm"
include "indif2.mm"
include "eqeq1i.mm"
include "ralrimi.mm"
include "wfn.mm"
include "wb.mm"
include "funfn.mm"
include "sseq1.mm"
include "ralrn.mm"
include "mpbird.mm"
include "pwssb.mm"
include "jca.mm"
include "elrnrexdm.mm"
include "nesym.mm"
include "nsyli.mm"
include "imp.mm"
include "reldisj.mm"
include "biimpd.mm"
include "sylc.mm"
include "impbii.mm"
include "syl6bb.mm"

theorem gneispace
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  let vx: setvar x
  assume gneispace.a: |- A = { f | ( f : dom f --> ( ~P ( ~P dom f \ { (/) } ) \ { (/) } ) /\ A. p e. dom f A. n e. ( f ` p ) ( p e. n /\ A. s e. ~P dom f ( n C_ s -> s e. ( f ` p ) ) ) ) }

  disjoint F n
  disjoint F p
  disjoint n p
  disjoint F f
  disjoint F s
  disjoint f s
  disjoint f n
  disjoint f p
  disjoint V p
  disjoint F x
  disjoint p x
  assert |- ( F e. V -> ( F e. A <-> ( Fun F /\ ran F C_ ~P ~P dom F /\ A. p e. dom F ( ( F ` p ) =/= (/) /\ A. n e. ( F ` p ) ( p e. n /\ A. s e. ~P dom F ( n C_ s -> s e. ( F ` p ) ) ) ) ) ) )

  proof
    cF
    cV
    wcel
    cF
    cA
    wcel
    cF
    wfun
    #
    cF
    crn
    #
    cF
    cdm
    #
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cpw
    #
    @4
    cdif
    #
    wss
    #
    wa
    #
    vp
    vn
    wel
    #
    vn
    cv
    vs
    cv
    #
    wss
    @11
    vp
    cv
    #
    cF
    cfv
    #
    wcel
    wi
    vs
    @3
    wral
    #
    wa
    #
    vn
    @13
    wral
    #
    vp
    @2
    wral
    #
    wa
    #
    @0
    @1
    @3
    cpw
    #
    wss
    #
    @13
    c0
    wne
    #
    @16
    wa
    #
    vp
    @2
    wral
    #
    w3a
    #
    cA
    vf
    vn
    cF
    cV
    vs
    vp
    gneispace.a
    gneispace3
    @18
    @24
    @18
    @0
    @20
    @23
    @0
    @8
    @17
    simpll
    @18
    @1
    @7
    @19
    @0
    @8
    @17
    simplr
    @7
    @6
    @19
    @6
    @4
    difss
    @5
    @3
    wss
    @6
    @19
    wss
    @3
    @4
    difss
    @5
    @3
    sspwb
    mpbi
    sstri
    syl6ss
    @9
    @21
    vp
    @2
    wral
    #
    @17
    @23
    @9
    @21
    vp
    @2
    @9
    @8
    @12
    @2
    wcel
    #
    @13
    @1
    wcel
    #
    @21
    @0
    @8
    simpr
    @9
    @0
    @26
    @27
    @0
    @8
    simpl
    @12
    cF
    fvelrn
    #
    sylan
    @8
    @27
    wa
    @13
    @7
    wcel
    @21
    @1
    @7
    @13
    ssel2
    @13
    @6
    c0
    eldifsni
    syl
    syl2an2r
    ralrimiva
    @23
    @25
    @17
    wa
    #
    @21
    @16
    vp
    @2
    r19.26
    #
    biimpri
    sylan
    3jca
    @24
    @9
    @17
    @24
    @0
    @8
    @0
    @20
    @23
    simp1
    #
    @24
    @1
    @6
    wss
    #
    @1
    @4
    cin
    c0
    wceq
    #
    @8
    @24
    vx
    cv
    #
    @5
    wss
    #
    vx
    @1
    wral
    #
    @32
    @24
    @36
    @13
    @5
    wss
    #
    vp
    @2
    wral
    #
    @24
    @37
    vp
    @2
    @0
    @20
    @23
    vp
    @0
    vp
    nfv
    @20
    vp
    nfv
    @22
    vp
    @2
    nfra1
    nf3an
    @24
    @26
    @13
    @3
    cin
    #
    @4
    cdif
    #
    @39
    wceq
    #
    @39
    @13
    wceq
    #
    wa
    #
    @37
    @24
    @26
    @41
    @42
    @24
    @26
    @10
    vp
    wex
    #
    vn
    @13
    wral
    #
    @41
    @24
    @45
    vp
    @2
    wral
    #
    @26
    @45
    wi
    @23
    @0
    @46
    @20
    @22
    @45
    vp
    @2
    @22
    @16
    @45
    @21
    @16
    simpr
    @15
    @44
    vn
    @13
    @15
    @10
    @44
    @10
    @14
    simpl
    @10
    vp
    19.8a
    syl
    ralimi
    syl
    ralimi
    3ad2ant3
    @45
    vp
    @2
    rsp
    syl
    @45
    @39
    @4
    cin
    c0
    wceq
    #
    @41
    @45
    c0
    @39
    wcel
    #
    wn
    @47
    @45
    c0
    @13
    wcel
    #
    @48
    @45
    @49
    wn
    @45
    @10
    wn
    vp
    wal
    #
    vn
    @13
    wrex
    #
    @49
    @45
    @50
    wn
    #
    vn
    @13
    wral
    @51
    wn
    @44
    @52
    vn
    @13
    @10
    vp
    df-ex
    ralbii
    @50
    vn
    @13
    ralnex
    bitri
    vn
    vp
    @13
    0el
    xchbinxr
    biimpi
    c0
    @13
    @3
    elinel1
    nsyl
    @39
    c0
    disjsn
    sylibr
    @39
    @4
    disjdif2
    syl
    syl6
    @24
    @20
    @26
    @27
    @42
    @0
    @20
    @23
    simp2
    @24
    @0
    @26
    @27
    wi
    @31
    @0
    @26
    @27
    @28
    ex
    syl
    @20
    @27
    wa
    @13
    @19
    wcel
    #
    @42
    @1
    @19
    @13
    ssel2
    @53
    @13
    @3
    wss
    @42
    @13
    @3
    @12
    cF
    fvex
    elpw
    @13
    @3
    df-ss
    sylbb
    syl
    syl6an
    jcad
    @43
    @40
    @13
    wceq
    #
    @37
    @40
    @39
    @13
    eqtr
    @37
    @13
    @5
    cin
    #
    @13
    wceq
    @54
    @13
    @5
    df-ss
    @55
    @40
    @13
    @13
    @3
    @4
    indif2
    eqeq1i
    bitri
    sylibr
    syl6
    ralrimi
    @24
    cF
    @2
    wfn
    #
    @36
    @38
    wb
    @24
    @0
    @56
    @31
    @0
    @56
    cF
    funfn
    biimpi
    syl
    @35
    @37
    vx
    vp
    @2
    cF
    @34
    @13
    @5
    sseq1
    ralrn
    syl
    mpbird
    vx
    @1
    @5
    pwssb
    sylibr
    @24
    @0
    @25
    wa
    #
    @33
    @24
    @0
    @25
    @31
    @23
    @0
    @25
    @20
    @22
    @21
    vp
    @2
    @21
    @16
    simpl
    ralimi
    3ad2ant3
    jca
    @57
    c0
    @1
    wcel
    #
    wn
    #
    @33
    @0
    @25
    @59
    @0
    @58
    c0
    @13
    wceq
    #
    vp
    @2
    wrex
    #
    @25
    vp
    cF
    c0
    elrnrexdm
    @25
    @60
    wn
    #
    vp
    @2
    wral
    @61
    wn
    @21
    @62
    vp
    @2
    @13
    c0
    nesym
    ralbii
    @60
    vp
    @2
    ralnex
    sylbb
    nsyli
    imp
    @1
    c0
    disjsn
    sylibr
    syl
    @32
    @33
    @8
    @1
    @4
    @6
    reldisj
    biimpd
    sylc
    jca
    @24
    @29
    @17
    @23
    @0
    @29
    @20
    @23
    @29
    @30
    biimpi
    3ad2ant3
    @25
    @17
    simpr
    syl
    jca
    impbii
    syl6bb
end
