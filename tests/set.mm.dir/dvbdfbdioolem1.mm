include "cv.mm"
include "cr.mm"
include "cicc.mm"
include "co.mm"
include "cres.mm"
include "cdv.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "wceq.mm"
include "cioo.mm"
include "wrex.mm"
include "cabs.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "ioossre.mm"
include "sseldi.mm"
include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "rexrd.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "wss.mm"
include "ccncf.mm"
include "iooltub.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "wf.mm"
include "cc.mm"
include "wb.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "cdm.mm"
include "fssd.mm"
include "dvcn.mm"
include "syl31anc.mm"
include "cncffvrn.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "rescncf.mm"
include "sylc.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "sstrd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "iccntr.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "ltled.mm"
include "ioossioo.mm"
include "sseqtr4d.mm"
include "ssdmres.mm"
include "sylib.mm"
include "mvth.mm"
include "w3a.mm"
include "fveq1d.mm"
include "fvres.mm"
include "sylan9eq.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "simp3.mm"
include "ubicc2.mm"
include "syl.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "3ad2ant1.mm"
include "3eqtrd.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "recnd.mm"
include "dvfre.mm"
include "feq2d.mm"
include "mpbid.mm"
include "adantr.mm"
include "sselda.mm"
include "cc0.mm"
include "wne.mm"
include "posdifd.mm"
include "gt0ne0d.mm"
include "divmul3d.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "abssubge0d.mm"
include "oveq2d.mm"
include "abscld.mm"
include "0red.mm"
include "wral.mm"
include "rspa.mm"
include "lemul1ad.mm"
include "eqbrtrd.mm"
include "syld3an3.mm"
include "absge0d.mm"
include "le2subd.mm"
include "lemul12ad.mm"
include "jca.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem dvbdfbdioolem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cK: class K
  let vk: setvar k
  assume dvbdfbdioolem1.a: |- ( ph -> A e. RR )
  assume dvbdfbdioolem1.b: |- ( ph -> B e. RR )
  assume dvbdfbdioolem1.f: |- ( ph -> F : ( A (,) B ) --> RR )
  assume dvbdfbdioolem1.dmdv: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume dvbdfbdioolem1.k: |- ( ph -> K e. RR )
  assume dvbdfbdioolem1.dvbd: |- ( ph -> A. x e. ( A (,) B ) ( abs ` ( ( RR _D F ) ` x ) ) <_ K )
  assume dvbdfbdioolem1.c: |- ( ph -> C e. ( A (,) B ) )
  assume dvbdfbdioolem1.d: |- ( ph -> D e. ( C (,) B ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint F x
  disjoint K x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( abs ` ( ( F ` D ) - ( F ` C ) ) ) <_ ( K x. ( D - C ) ) /\ ( abs ` ( ( F ` D ) - ( F ` C ) ) ) <_ ( K x. ( B - A ) ) ) )

  proof
    wph
    vx
    cv
    #
    cr
    cF
    cC
    cD
    cicc
    co
    #
    cres
    #
    cdv
    co
    #
    cfv
    #
    cD
    @2
    cfv
    #
    cC
    @2
    cfv
    #
    cmin
    co
    #
    cD
    cC
    cmin
    co
    #
    cdiv
    co
    #
    wceq
    #
    vx
    cC
    cD
    cioo
    co
    #
    wrex
    cD
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cK
    @8
    cmul
    co
    #
    cle
    wbr
    #
    @15
    cK
    cB
    cA
    cmin
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    wph
    vx
    cC
    cD
    @2
    wph
    cA
    cB
    cioo
    co
    #
    cr
    cC
    cA
    cB
    ioossre
    #
    dvbdfbdioolem1.c
    sseldi
    #
    wph
    cC
    cB
    cioo
    co
    #
    cr
    cD
    cC
    cB
    ioossre
    dvbdfbdioolem1.d
    sseldi
    #
    wph
    cC
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cD
    @25
    wcel
    #
    cC
    cD
    clt
    wbr
    #
    wph
    cC
    @24
    rexrd
    #
    wph
    cB
    dvbdfbdioolem1.b
    rexrd
    #
    dvbdfbdioolem1.d
    cC
    cB
    cD
    ioogtlb
    syl3anc
    #
    wph
    @1
    @22
    wss
    #
    cF
    @22
    cr
    ccncf
    co
    wcel
    #
    @2
    @1
    cr
    ccncf
    co
    wcel
    wph
    cA
    cxr
    wcel
    #
    @28
    cA
    cC
    clt
    wbr
    #
    cD
    cB
    clt
    wbr
    #
    @34
    wph
    cA
    dvbdfbdioolem1.a
    rexrd
    #
    @32
    wph
    @36
    @28
    cC
    @22
    wcel
    @37
    @39
    @32
    dvbdfbdioolem1.c
    cA
    cB
    cC
    ioogtlb
    syl3anc
    #
    wph
    @27
    @28
    @29
    @38
    @31
    @32
    dvbdfbdioolem1.d
    cC
    cB
    cD
    iooltub
    syl3anc
    #
    cA
    cB
    cC
    cD
    iccssioo
    syl22anc
    #
    wph
    @35
    @22
    cr
    cF
    wf
    #
    dvbdfbdioolem1.f
    wph
    cr
    cc
    wss
    #
    cF
    @22
    cc
    ccncf
    co
    wcel
    #
    @35
    @43
    wb
    @44
    wph
    ax-resscn
    a1i
    #
    wph
    @44
    @22
    cc
    cF
    wf
    #
    @22
    cr
    wss
    #
    cr
    cF
    cdv
    co
    #
    cdm
    #
    @22
    wceq
    @45
    @46
    wph
    @22
    cr
    cc
    cF
    dvbdfbdioolem1.f
    @46
    fssd
    #
    @48
    wph
    @23
    a1i
    #
    dvbdfbdioolem1.dmdv
    @22
    cr
    cF
    dvcn
    syl31anc
    @22
    cc
    cr
    cF
    cncffvrn
    syl2anc
    mpbird
    @22
    cr
    @1
    cF
    rescncf
    sylc
    wph
    @3
    cdm
    @49
    @11
    cres
    #
    cdm
    #
    @11
    wph
    @3
    @53
    wph
    @3
    @49
    @1
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @53
    wph
    @44
    @47
    @48
    @1
    cr
    wss
    @3
    @57
    wceq
    @46
    @51
    @52
    wph
    @1
    @22
    cr
    @42
    @52
    sstrd
    @22
    @1
    cr
    @55
    cF
    ccnfld
    ctopn
    cfv
    #
    @58
    eqid
    #
    @58
    @59
    tgioo2
    dvres
    syl22anc
    wph
    @56
    @11
    @49
    wph
    cC
    cr
    wcel
    cD
    cr
    wcel
    @56
    @11
    wceq
    @24
    @26
    cC
    cD
    iccntr
    syl2anc
    reseq2d
    eqtrd
    #
    dmeqd
    wph
    @11
    @50
    wss
    @54
    @11
    wceq
    wph
    @11
    @22
    @50
    wph
    @36
    @28
    cA
    cC
    cle
    wbr
    cD
    cB
    cle
    wbr
    @11
    @22
    wss
    @39
    @32
    wph
    cA
    cC
    dvbdfbdioolem1.a
    @24
    @40
    ltled
    #
    wph
    cD
    cB
    @26
    dvbdfbdioolem1.b
    @41
    ltled
    #
    cA
    cB
    cC
    cD
    ioossioo
    syl22anc
    #
    dvbdfbdioolem1.dmdv
    sseqtr4d
    @11
    @49
    ssdmres
    sylib
    eqtrd
    mvth
    wph
    @10
    @21
    vx
    @11
    wph
    @0
    @11
    wcel
    #
    @10
    w3a
    #
    @17
    @20
    wph
    @64
    @10
    @0
    @49
    cfv
    #
    @14
    @8
    cdiv
    co
    #
    wceq
    #
    @17
    @65
    @66
    @4
    @9
    @67
    wph
    @64
    @66
    @4
    wceq
    @10
    wph
    @64
    wa
    #
    @4
    @66
    wph
    @64
    @4
    @0
    @53
    cfv
    @66
    wph
    @0
    @3
    @53
    @60
    fveq1d
    @0
    @11
    @49
    fvres
    sylan9eq
    eqcomd
    3adant3
    wph
    @64
    @10
    simp3
    wph
    @64
    @9
    @67
    wceq
    @10
    wph
    @7
    @14
    @8
    cdiv
    wph
    @5
    @12
    @6
    @13
    cmin
    wph
    cD
    @1
    wcel
    #
    @5
    @12
    wceq
    wph
    @27
    cD
    cxr
    wcel
    #
    cC
    cD
    cle
    wbr
    #
    @70
    @31
    wph
    cD
    @26
    rexrd
    #
    wph
    cC
    cD
    @24
    @26
    @33
    ltled
    #
    cC
    cD
    ubicc2
    syl3anc
    #
    cD
    @1
    cF
    fvres
    syl
    wph
    cC
    @1
    wcel
    #
    @6
    @13
    wceq
    wph
    @27
    @71
    @72
    @76
    @31
    @73
    @74
    cC
    cD
    lbicc2
    syl3anc
    cC
    @1
    cF
    fvres
    syl
    oveq12d
    oveq1d
    3ad2ant1
    3eqtrd
    #
    wph
    @64
    @68
    w3a
    #
    @15
    @66
    cabs
    cfv
    #
    @8
    cmul
    co
    #
    @16
    cle
    @78
    @15
    @79
    @8
    cabs
    cfv
    #
    cmul
    co
    #
    @80
    @78
    @15
    @66
    @8
    cmul
    co
    #
    cabs
    cfv
    #
    @82
    @78
    @14
    @83
    cabs
    @78
    @67
    @66
    wceq
    @14
    @83
    wceq
    @78
    @66
    @67
    wph
    @64
    @68
    simp3
    eqcomd
    @78
    @14
    @66
    @8
    wph
    @64
    @14
    cc
    wcel
    @68
    wph
    @14
    wph
    @12
    @13
    wph
    @22
    cr
    cD
    cF
    dvbdfbdioolem1.f
    wph
    @1
    @22
    cD
    @42
    @75
    sseldd
    ffvelrnd
    wph
    @22
    cr
    cC
    cF
    dvbdfbdioolem1.f
    dvbdfbdioolem1.c
    ffvelrnd
    resubcld
    recnd
    3ad2ant1
    wph
    @64
    @66
    cc
    wcel
    @68
    @69
    @66
    @69
    @22
    cr
    @0
    @49
    wph
    @22
    cr
    @49
    wf
    #
    @64
    wph
    @50
    cr
    @49
    wf
    #
    @85
    wph
    @43
    @48
    @86
    dvbdfbdioolem1.f
    @52
    @22
    cF
    dvfre
    syl2anc
    wph
    @50
    @22
    cr
    @49
    dvbdfbdioolem1.dmdv
    feq2d
    mpbid
    adantr
    wph
    @11
    @22
    @0
    @63
    sselda
    #
    ffvelrnd
    recnd
    #
    3adant3
    wph
    @64
    @8
    cc
    wcel
    #
    @68
    wph
    @8
    wph
    cD
    cC
    @26
    @24
    resubcld
    #
    recnd
    #
    3ad2ant1
    wph
    @64
    @8
    cc0
    wne
    @68
    wph
    @8
    wph
    @30
    cc0
    @8
    clt
    wbr
    @33
    wph
    cC
    cD
    @24
    @26
    posdifd
    mpbid
    #
    gt0ne0d
    3ad2ant1
    divmul3d
    mpbid
    fveq2d
    wph
    @64
    @84
    @82
    wceq
    @68
    @69
    @66
    @8
    @88
    wph
    @89
    @64
    @91
    adantr
    #
    absmuld
    3adant3
    eqtrd
    #
    wph
    @64
    @82
    @80
    wceq
    @68
    wph
    @81
    @8
    @79
    cmul
    wph
    cC
    cD
    @24
    @26
    @74
    abssubge0d
    #
    oveq2d
    3ad2ant1
    eqtrd
    wph
    @64
    @80
    @16
    cle
    wbr
    @68
    @69
    @79
    cK
    @8
    @69
    @66
    @88
    abscld
    #
    wph
    cK
    cr
    wcel
    @64
    dvbdfbdioolem1.k
    adantr
    #
    wph
    @8
    cr
    wcel
    @64
    @90
    adantr
    wph
    cc0
    @8
    cle
    wbr
    @64
    wph
    cc0
    @8
    wph
    0red
    @90
    @92
    ltled
    adantr
    @69
    @79
    cK
    cle
    wbr
    #
    vx
    @22
    wral
    #
    @0
    @22
    wcel
    @98
    wph
    @99
    @64
    dvbdfbdioolem1.dvbd
    adantr
    @87
    @98
    vx
    @22
    rspa
    syl2anc
    #
    lemul1ad
    3adant3
    eqbrtrd
    syld3an3
    wph
    @64
    @10
    @68
    @20
    @77
    @78
    @15
    @82
    @19
    cle
    @94
    wph
    @64
    @82
    @19
    cle
    wbr
    @68
    @69
    @79
    cK
    @81
    @18
    @96
    @97
    @69
    @8
    @93
    abscld
    wph
    @18
    cr
    wcel
    @64
    wph
    cB
    cA
    dvbdfbdioolem1.b
    dvbdfbdioolem1.a
    resubcld
    adantr
    @69
    @66
    @88
    absge0d
    @69
    @8
    @93
    absge0d
    @100
    wph
    @81
    @18
    cle
    wbr
    @64
    wph
    @81
    @8
    @18
    cle
    @95
    wph
    cD
    cA
    cB
    cC
    @26
    dvbdfbdioolem1.a
    dvbdfbdioolem1.b
    @24
    @62
    @61
    le2subd
    eqbrtrd
    adantr
    lemul12ad
    3adant3
    eqbrtrd
    syld3an3
    jca
    rexlimdv3a
    mpd
end
