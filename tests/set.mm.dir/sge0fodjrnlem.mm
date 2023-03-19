include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "wcel.mm"
include "wfo.mm"
include "fornex.mm"
include "sylc.mm"
include "difssd.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "simpl.mm"
include "sselda.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cin.mm"
include "dfin4.mm"
include "eqcomi.mm"
include "inss2.mm"
include "eqsstri.mm"
include "id.mm"
include "sseldi.mm"
include "elsni.mm"
include "syl.mm"
include "adantl.mm"
include "sge0ss.mm"
include "eqcomd.mm"
include "cres.mm"
include "difexg.mm"
include "wf1o.mm"
include "wne.mm"
include "crab.mm"
include "crn.mm"
include "eqid.mm"
include "wf.mm"
include "fof.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "cbvrabv.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "difeq1i.mm"
include "disjf1o.mm"
include "feqmptd.mm"
include "wb.mm"
include "wal.mm"
include "ccnv.mm"
include "cima.mm"
include "eldifi.mm"
include "adantr.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "jca.mm"
include "adantll.mm"
include "wfn.mm"
include "ffnd.mm"
include "elpreima.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "syl6eleqr.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "elrab.mm"
include "ex.mm"
include "wral.mm"
include "wss.mm"
include "simplbi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "mpbid.mm"
include "simprd.mm"
include "adantlr.mm"
include "simprbi.mm"
include "neneqd.mm"
include "eldifd.mm"
include "ralrimi.mm"
include "dfss3.mm"
include "sseld.mm"
include "impbid.mm"
include "alrimi.mm"
include "dfcleq.mm"
include "reseq12d.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "forn.mm"
include "eqtr2d.mm"
include "difeq1d.mm"
include "f1oeq123d.mm"
include "fvres.mm"
include "eqtrd.mm"
include "sge0f1o.mm"
include "eqeltrd.mm"
include "imdistani.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "difss.mm"
include "syl6eleq.mm"
include "elind.mm"
include "simpld.mm"
include "eqeq1.mm"
include "eqeq1d.mm"
include "3eqtrd.mm"

theorem sge0fodjrnlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z
  let vm: setvar m
  let vx: setvar x
  assume sge0fodjrnlem.k: |- F/ k ph
  assume sge0fodjrnlem.n: |- F/ n ph
  assume sge0fodjrnlem.bd: |- ( k = G -> B = D )
  assume sge0fodjrnlem.c: |- ( ph -> C e. V )
  assume sge0fodjrnlem.f: |- ( ph -> F : C -onto-> A )
  assume sge0fodjrnlem.dj: |- ( ph -> Disj_ n e. C ( F ` n ) )
  assume sge0fodjrnlem.fng: |- ( ( ph /\ n e. C ) -> ( F ` n ) = G )
  assume sge0fodjrnlem.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0fodjrnlem.b0: |- ( ( ph /\ k = (/) ) -> B = 0 )
  assume sge0fodjrnlem.z: |- Z = ( `' F " { (/) } )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint B n
  disjoint C k
  disjoint C n
  disjoint D k
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint Z k
  disjoint Z n
  disjoint C m
  disjoint m n
  disjoint F m
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) = ( sum^ ` ( n e. C |-> D ) ) )

  proof
    wph
    vk
    cA
    cB
    cmpt
    csumge0
    cfv
    #
    vk
    cA
    c0
    csn
    #
    cdif
    #
    cB
    cmpt
    csumge0
    cfv
    #
    vn
    cC
    cZ
    cdif
    #
    cD
    cmpt
    csumge0
    cfv
    vn
    cC
    cD
    cmpt
    csumge0
    cfv
    wph
    @3
    @0
    wph
    @2
    cA
    cB
    vk
    cvv
    sge0fodjrnlem.k
    wph
    cC
    cV
    wcel
    #
    cC
    cA
    cF
    wfo
    #
    cA
    cvv
    wcel
    sge0fodjrnlem.c
    sge0fodjrnlem.f
    cC
    cA
    cV
    cF
    fornex
    sylc
    wph
    cA
    @1
    difssd
    #
    wph
    vk
    cv
    #
    @2
    wcel
    #
    wa
    wph
    @8
    cA
    wcel
    #
    cB
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    wph
    @9
    simpl
    wph
    @2
    cA
    @8
    @7
    sselda
    sge0fodjrnlem.b
    syl2anc
    #
    wph
    @8
    cA
    @2
    cdif
    #
    wcel
    #
    wa
    wph
    @8
    c0
    wceq
    #
    cB
    cc0
    wceq
    #
    wph
    @15
    simpl
    @15
    @16
    wph
    @15
    @8
    @1
    wcel
    @16
    @15
    @14
    @1
    @8
    @14
    cA
    @1
    cin
    #
    @1
    @18
    @14
    cA
    @1
    dfin4
    eqcomi
    cA
    @1
    inss2
    eqsstri
    @15
    id
    sseldi
    @8
    c0
    elsni
    syl
    adantl
    sge0fodjrnlem.b0
    syl2anc
    sge0ss
    eqcomd
    wph
    @2
    cB
    @4
    cD
    vk
    vn
    cF
    @4
    cres
    #
    cG
    cvv
    sge0fodjrnlem.k
    sge0fodjrnlem.n
    sge0fodjrnlem.bd
    wph
    @5
    @4
    cvv
    wcel
    sge0fodjrnlem.c
    cC
    cZ
    cV
    difexg
    syl
    wph
    @4
    @2
    @19
    wf1o
    vm
    cv
    #
    cF
    cfv
    #
    c0
    wne
    #
    vm
    cC
    crab
    #
    vm
    cC
    @21
    cmpt
    #
    crn
    #
    @1
    cdif
    #
    vn
    cC
    vn
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    @23
    cres
    #
    wf1o
    wph
    vn
    cC
    @28
    @23
    @26
    @29
    cA
    sge0fodjrnlem.n
    @29
    eqid
    wph
    cC
    cA
    @27
    cF
    wph
    @6
    cC
    cA
    cF
    wf
    sge0fodjrnlem.f
    cC
    cA
    cF
    fof
    syl
    #
    ffvelrnda
    #
    sge0fodjrnlem.dj
    @22
    @28
    c0
    wne
    #
    vm
    vn
    cC
    @20
    @27
    wceq
    @21
    @28
    c0
    @20
    @27
    cF
    fveq2
    #
    neeq1d
    #
    cbvrabv
    @25
    @29
    crn
    @1
    @24
    @29
    vm
    vn
    cC
    @21
    @28
    @34
    cbvmptv
    #
    rneqi
    difeq1i
    disjf1o
    wph
    @4
    @23
    @2
    @26
    @19
    @30
    wph
    cF
    @29
    @4
    @23
    wph
    vn
    cC
    cA
    cF
    @31
    feqmptd
    #
    wph
    @27
    @4
    wcel
    #
    @27
    @23
    wcel
    #
    wb
    #
    vn
    wal
    @4
    @23
    wceq
    wph
    @40
    vn
    sge0fodjrnlem.n
    wph
    @38
    @39
    wph
    @38
    @39
    wph
    @38
    wa
    #
    @27
    cC
    wcel
    #
    @33
    wa
    @39
    @41
    @42
    @33
    wph
    @4
    cC
    @27
    wph
    cC
    cZ
    difssd
    #
    sselda
    #
    @41
    @28
    c0
    @41
    @28
    c0
    wceq
    #
    @27
    cZ
    wcel
    #
    @41
    @45
    wa
    #
    @27
    cF
    ccnv
    @1
    cima
    #
    cZ
    @47
    @27
    @48
    wcel
    #
    @42
    @28
    @1
    wcel
    #
    wa
    #
    @38
    @45
    @51
    wph
    @38
    @45
    wa
    @42
    @50
    @38
    @42
    @45
    @27
    cC
    cZ
    eldifi
    adantr
    @45
    @50
    @38
    @45
    @45
    @50
    @45
    id
    @28
    c0
    @27
    cF
    fvex
    elsn
    sylibr
    adantl
    jca
    adantll
    wph
    @49
    @51
    wb
    #
    @38
    @45
    wph
    cF
    cC
    wfn
    @52
    wph
    cC
    cA
    cF
    @31
    ffnd
    cC
    @27
    @1
    cF
    elpreima
    syl
    #
    ad2antrr
    mpbird
    sge0fodjrnlem.z
    syl6eleqr
    @38
    @46
    wn
    wph
    @45
    @27
    cC
    cZ
    eldifn
    ad2antlr
    pm2.65da
    neqned
    jca
    @22
    @33
    vm
    @27
    cC
    @35
    elrab
    #
    sylibr
    ex
    wph
    @23
    @4
    @27
    wph
    @38
    vn
    @23
    wral
    @23
    @4
    wss
    wph
    @38
    vn
    @23
    sge0fodjrnlem.n
    wph
    @39
    @38
    wph
    @39
    wa
    #
    @27
    cC
    cZ
    @39
    @42
    wph
    @39
    @42
    @33
    @54
    simplbi
    adantl
    @55
    @46
    @45
    wph
    @46
    @45
    @39
    wph
    @46
    wa
    #
    @50
    @45
    @56
    @42
    @50
    @56
    @49
    @51
    @46
    @49
    wph
    @46
    @49
    cZ
    @48
    @27
    sge0fodjrnlem.z
    eleq2i
    biimpi
    adantl
    wph
    @52
    @46
    @53
    adantr
    mpbid
    #
    simprd
    @28
    c0
    elsni
    syl
    #
    adantlr
    @55
    @46
    wa
    @28
    c0
    @39
    @33
    wph
    @46
    @39
    @42
    @33
    @54
    simprbi
    ad2antlr
    neneqd
    pm2.65da
    eldifd
    ex
    ralrimi
    vn
    @23
    @4
    dfss3
    sylibr
    sseld
    impbid
    alrimi
    vn
    @4
    @23
    dfcleq
    sylibr
    #
    reseq12d
    @59
    wph
    cA
    @25
    @1
    wph
    @25
    cF
    crn
    #
    cA
    wph
    @24
    cF
    wph
    cF
    @24
    wph
    cF
    @29
    @24
    @37
    @36
    syl6eqr
    eqcomd
    rneqd
    wph
    @6
    @60
    cA
    wceq
    sge0fodjrnlem.f
    cC
    cA
    cF
    forn
    syl
    eqtr2d
    difeq1d
    f1oeq123d
    mpbird
    @41
    @27
    @19
    cfv
    #
    @28
    cG
    @38
    @61
    @28
    wceq
    wph
    @27
    @4
    cF
    fvres
    adantl
    @41
    wph
    @42
    @28
    cG
    wceq
    #
    wph
    @38
    simpl
    #
    @44
    sge0fodjrnlem.fng
    syl2anc
    eqtrd
    @13
    sge0f1o
    wph
    @4
    cC
    cD
    vn
    cV
    sge0fodjrnlem.n
    sge0fodjrnlem.c
    @43
    @41
    cG
    cA
    wcel
    #
    wph
    @64
    wa
    #
    cD
    @11
    wcel
    #
    @41
    wph
    @42
    @64
    @63
    @44
    wph
    @42
    wa
    #
    cG
    @28
    cA
    @67
    @28
    cG
    sge0fodjrnlem.fng
    eqcomd
    @32
    eqeltrd
    #
    syl2anc
    #
    wph
    @38
    @64
    wph
    @38
    @64
    @69
    ex
    imdistani
    wph
    @10
    wa
    #
    @12
    wi
    @65
    @66
    wi
    vk
    cG
    cA
    vk
    cG
    nfcv
    #
    @65
    @66
    vk
    wph
    @64
    vk
    sge0fodjrnlem.k
    @64
    vk
    nfv
    nfan
    @66
    vk
    nfv
    nfim
    @8
    cG
    wceq
    #
    @70
    @65
    @12
    @66
    @72
    @10
    @64
    wph
    @8
    cG
    cA
    eleq1
    anbi2d
    @72
    cB
    cD
    @11
    sge0fodjrnlem.bd
    eleq1d
    imbi12d
    sge0fodjrnlem.b
    vtoclgf
    sylc
    wph
    @27
    cC
    @4
    cdif
    #
    wcel
    #
    wa
    #
    @64
    wph
    cG
    c0
    wceq
    #
    wa
    #
    cD
    cc0
    wceq
    #
    @75
    wph
    @42
    @64
    wph
    @74
    simpl
    #
    @74
    @42
    wph
    @27
    cC
    @4
    eldifi
    #
    adantl
    @68
    syl2anc
    @75
    wph
    @76
    @79
    @75
    wph
    @46
    @76
    @79
    @74
    @46
    wph
    @74
    cZ
    cC
    cin
    #
    cZ
    @27
    @81
    cZ
    cZ
    cC
    cdif
    #
    cdif
    cZ
    cZ
    cC
    dfin4
    cZ
    @82
    difss
    eqsstri
    @74
    cZ
    cC
    @27
    @74
    cC
    cZ
    cin
    #
    cZ
    @27
    cC
    cZ
    inss2
    @74
    @27
    @73
    @83
    @74
    id
    @83
    @73
    cC
    cZ
    dfin4
    eqcomi
    syl6eleq
    sseldi
    @80
    elind
    sseldi
    adantl
    @56
    c0
    @28
    cG
    @56
    @28
    c0
    @58
    eqcomd
    @56
    wph
    @42
    @62
    wph
    @46
    simpl
    @56
    @42
    @50
    @57
    simpld
    sge0fodjrnlem.fng
    syl2anc
    eqtr2d
    syl2anc
    jca
    wph
    @16
    wa
    #
    @17
    wi
    @77
    @78
    wi
    vk
    cG
    cA
    @71
    @77
    @78
    vk
    wph
    @76
    vk
    sge0fodjrnlem.k
    @76
    vk
    nfv
    nfan
    @78
    vk
    nfv
    nfim
    @72
    @84
    @77
    @17
    @78
    @72
    @16
    @76
    wph
    @8
    cG
    c0
    eqeq1
    anbi2d
    @72
    cB
    cD
    cc0
    sge0fodjrnlem.bd
    eqeq1d
    imbi12d
    sge0fodjrnlem.b0
    vtoclgf
    sylc
    sge0ss
    3eqtrd
end
