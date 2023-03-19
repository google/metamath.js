include "cioo.mm"
include "co.mm"
include "cr.mm"
include "cdv.mm"
include "wf.mm"
include "cv.mm"
include "caddc.mm"
include "cres.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "csin.mm"
include "cmul.mm"
include "ccos.mm"
include "cmin.mm"
include "cexp.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wcel.mm"
include "adantr.mm"
include "cxr.mm"
include "readdcld.mm"
include "rexrd.mm"
include "elioore.mm"
include "adantl.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltadd2dd.mm"
include "iooltub.mm"
include "eliood.mm"
include "ffvelrnd.mm"
include "2re.mm"
include "a1i.mm"
include "rehalfcl.mm"
include "syl.mm"
include "resincld.mm"
include "remulcld.mm"
include "recoscld.mm"
include "resubcld.mm"
include "resqcld.mm"
include "cc.mm"
include "2cnd.mm"
include "recnd.mm"
include "sincld.mm"
include "mulcld.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "sselda.mm"
include "eqcom.mm"
include "biimpi.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "neqned.mm"
include "fourierdlem44.mm"
include "syl2anc.mm"
include "mulne0d.mm"
include "cz.mm"
include "2z.mm"
include "expne0d.mm"
include "redivcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "oveq2d.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "fourierdlem28.mm"
include "0red.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "crn.mm"
include "ctg.mm"
include "iooretop.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "dvmptconst.mm"
include "dvmptsub.mm"
include "subid1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "c1.mm"
include "recn.mm"
include "divrec2d.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "halfcn.mm"
include "id.mm"
include "coscld.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "cnt.mm"
include "wss.mm"
include "ioossre.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "ax-resscn.mm"
include "fmpti.mm"
include "ssid.mm"
include "dvres.mm"
include "mp4an.mm"
include "mpteq2ia.mm"
include "eqtr2i.mm"
include "ioontr.mm"
include "reseq12i.mm"
include "cdm.mm"
include "dmmptg.mm"
include "2cn.mm"
include "mulcli.mm"
include "mprg.mm"
include "sseqtr4i.mm"
include "dvasinbx.mm"
include "mp2an.mm"
include "dmeqi.mm"
include "dvres3.mm"
include "reseq1i.mm"
include "resabs1.mm"
include "ioosscn.mm"
include "3eqtri.mm"
include "recidi.mm"
include "oveq1i.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "eqtri.mm"
include "dvmptdiv.mm"
include "feq1d.mm"
include "mpbird.mm"
include "jca.mm"
include "pm3.2i.mm"

theorem fourierdlem57
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cO: class O
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem57.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem57.xre: |- ( ph -> X e. RR )
  assume fourierdlem57.a: |- ( ph -> A e. RR )
  assume fourierdlem57.b: |- ( ph -> B e. RR )
  assume fourierdlem57.fdv: |- ( ph -> ( RR _D ( F |` ( ( X + A ) (,) ( X + B ) ) ) ) : ( ( X + A ) (,) ( X + B ) ) --> RR )
  assume fourierdlem57.ab: |- ( ph -> ( A (,) B ) C_ ( -u _pi [,] _pi ) )
  assume fourierdlem57.n0: |- ( ph -> -. 0 e. ( A (,) B ) )
  assume fourierdlem57.c: |- ( ph -> C e. RR )
  assume fourierdlem57.o: |- O = ( s e. ( A (,) B ) |-> ( ( ( F ` ( X + s ) ) - C ) / ( 2 x. ( sin ` ( s / 2 ) ) ) ) )

  disjoint A s
  disjoint B s
  disjoint C s
  disjoint F s
  disjoint X s
  disjoint ph s
  disjoint k x
  assert |- ( ( ph -> ( ( RR _D O ) : ( A (,) B ) --> RR /\ ( RR _D O ) = ( s e. ( A (,) B ) |-> ( ( ( ( ( RR _D ( F |` ( ( X + A ) (,) ( X + B ) ) ) ) ` ( X + s ) ) x. ( 2 x. ( sin ` ( s / 2 ) ) ) ) - ( ( cos ` ( s / 2 ) ) x. ( ( F ` ( X + s ) ) - C ) ) ) / ( ( 2 x. ( sin ` ( s / 2 ) ) ) ^ 2 ) ) ) ) ) /\ ( RR _D ( s e. ( A (,) B ) |-> ( 2 x. ( sin ` ( s / 2 ) ) ) ) ) = ( s e. ( A (,) B ) |-> ( cos ` ( s / 2 ) ) ) )

  proof
    wph
    cA
    cB
    cioo
    co
    #
    cr
    cr
    cO
    cdv
    co
    #
    wf
    #
    @1
    vs
    @0
    cX
    vs
    cv
    #
    caddc
    co
    #
    cr
    cF
    cX
    cA
    caddc
    co
    #
    cX
    cB
    caddc
    co
    #
    cioo
    co
    #
    cres
    cdv
    co
    #
    cfv
    #
    c2
    @3
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @10
    ccos
    cfv
    #
    @4
    cF
    cfv
    #
    cC
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    @12
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    wceq
    #
    wa
    wi
    cr
    vs
    @0
    @12
    cmpt
    #
    cdv
    co
    #
    vs
    @0
    @14
    cmpt
    #
    wceq
    #
    wph
    @2
    @22
    wph
    @2
    @0
    cr
    @21
    wf
    wph
    vs
    @0
    @20
    cr
    @21
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @18
    @19
    @28
    @13
    @17
    @28
    @9
    @12
    @28
    @7
    cr
    @4
    @8
    wph
    @7
    cr
    @8
    wf
    @27
    fourierdlem57.fdv
    adantr
    @28
    @5
    @6
    @4
    wph
    @5
    cxr
    wcel
    @27
    wph
    @5
    wph
    cX
    cA
    fourierdlem57.xre
    fourierdlem57.a
    readdcld
    rexrd
    adantr
    wph
    @6
    cxr
    wcel
    @27
    wph
    @6
    wph
    cX
    cB
    fourierdlem57.xre
    fourierdlem57.b
    readdcld
    rexrd
    adantr
    @28
    cX
    @3
    wph
    cX
    cr
    wcel
    @27
    fourierdlem57.xre
    adantr
    #
    @27
    @3
    cr
    wcel
    #
    wph
    @3
    cA
    cB
    elioore
    #
    adantl
    #
    readdcld
    #
    @28
    cA
    @3
    cX
    wph
    cA
    cr
    wcel
    @27
    fourierdlem57.a
    adantr
    #
    @32
    @29
    @28
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @27
    cA
    @3
    clt
    wbr
    @28
    cA
    @34
    rexrd
    #
    wph
    @36
    @27
    wph
    cB
    fourierdlem57.b
    rexrd
    adantr
    #
    wph
    @27
    simpr
    #
    cA
    cB
    @3
    ioogtlb
    syl3anc
    ltadd2dd
    @28
    @3
    cB
    cX
    @32
    wph
    cB
    cr
    wcel
    @27
    fourierdlem57.b
    adantr
    @29
    @28
    @35
    @36
    @27
    @3
    cB
    clt
    wbr
    @37
    @38
    @39
    cA
    cB
    @3
    iooltub
    syl3anc
    ltadd2dd
    eliood
    ffvelrnd
    #
    @28
    c2
    @11
    c2
    cr
    wcel
    @28
    2re
    a1i
    @28
    @10
    @28
    @30
    @10
    cr
    wcel
    @32
    @3
    rehalfcl
    #
    syl
    #
    resincld
    remulcld
    #
    remulcld
    @28
    @14
    @16
    @28
    @10
    @42
    recoscld
    @28
    @15
    cC
    @28
    cr
    cr
    @4
    cF
    wph
    cr
    cr
    cF
    wf
    @27
    fourierdlem57.f
    adantr
    @33
    ffvelrnd
    #
    wph
    cC
    cr
    wcel
    @27
    fourierdlem57.c
    adantr
    #
    resubcld
    #
    remulcld
    resubcld
    @28
    @12
    @43
    resqcld
    @28
    @12
    c2
    @28
    @30
    @12
    cc
    wcel
    #
    @32
    @30
    c2
    @11
    @30
    2cnd
    #
    @30
    @10
    @30
    @10
    @41
    recnd
    sincld
    #
    mulcld
    #
    syl
    #
    @28
    c2
    @11
    @28
    2cnd
    @28
    @30
    @11
    cc
    wcel
    @32
    @49
    syl
    c2
    cc0
    wne
    #
    @28
    2ne0
    a1i
    @28
    @3
    cpi
    cneg
    cpi
    cicc
    co
    #
    wcel
    @3
    cc0
    wne
    @11
    cc0
    wne
    wph
    @0
    @53
    @3
    fourierdlem57.ab
    sselda
    @28
    @3
    cc0
    @28
    @3
    cc0
    wceq
    #
    cc0
    @0
    wcel
    #
    @27
    @54
    @55
    wph
    @27
    @54
    wa
    cc0
    @3
    @0
    @54
    cc0
    @3
    wceq
    #
    @27
    @54
    @56
    @3
    cc0
    eqcom
    biimpi
    adantl
    @27
    @54
    simpl
    eqeltrd
    adantll
    wph
    @55
    wn
    @27
    @54
    fourierdlem57.n0
    ad2antrr
    pm2.65da
    neqned
    @3
    fourierdlem44
    syl2anc
    mulne0d
    #
    c2
    cz
    wcel
    @28
    2z
    a1i
    expne0d
    redivcld
    @21
    eqid
    fmptd
    wph
    @0
    cr
    @1
    @21
    wph
    @1
    cr
    vs
    @0
    @16
    @12
    cdiv
    co
    cmpt
    #
    cdv
    co
    @21
    wph
    cO
    @58
    cr
    cdv
    cO
    @58
    wceq
    wph
    fourierdlem57.o
    a1i
    oveq2d
    wph
    vs
    @16
    @9
    @12
    @14
    cr
    cr
    @0
    cr
    cr
    cc
    cpr
    wcel
    #
    wph
    reelprrecn
    a1i
    #
    @28
    @16
    @46
    recnd
    @40
    wph
    cr
    vs
    @0
    @16
    cmpt
    cdv
    co
    vs
    @0
    @9
    cc0
    cmin
    co
    #
    cmpt
    vs
    @0
    @9
    cmpt
    wph
    vs
    @15
    @9
    cC
    cc0
    cr
    cr
    cr
    @0
    @60
    @28
    @15
    @44
    recnd
    @40
    wph
    cA
    cB
    @8
    cF
    cX
    vs
    fourierdlem57.f
    fourierdlem57.xre
    fourierdlem57.a
    fourierdlem57.b
    @8
    eqid
    fourierdlem57.fdv
    fourierdlem28
    @28
    cC
    @45
    recnd
    @28
    0red
    wph
    vs
    @0
    cC
    cr
    @60
    @0
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    wph
    @0
    cioo
    crn
    ctg
    cfv
    #
    @63
    cA
    cB
    iooretop
    @62
    @62
    eqid
    #
    tgioo2
    #
    eleqtri
    a1i
    wph
    cC
    fourierdlem57.c
    recnd
    dvmptconst
    dvmptsub
    wph
    vs
    @0
    @61
    @9
    @28
    @9
    @28
    @9
    @40
    recnd
    subid1d
    mpteq2dva
    eqtrd
    @28
    @47
    @12
    cc0
    wne
    @12
    cc
    cc0
    csn
    cdif
    wcel
    @51
    @57
    @12
    cc
    cc0
    eldifsn
    sylanbrc
    @27
    @14
    cc
    wcel
    wph
    @27
    c1
    c2
    cdiv
    co
    #
    @3
    cmul
    co
    #
    ccos
    cfv
    #
    @14
    cc
    @27
    @68
    @10
    ccos
    @27
    @30
    @68
    @10
    wceq
    @31
    @30
    @10
    @68
    @30
    @3
    c2
    @3
    recn
    #
    @48
    @52
    @30
    2ne0
    a1i
    divrec2d
    eqcomd
    #
    syl
    fveq2d
    #
    @27
    @30
    @3
    cc
    wcel
    #
    @69
    cc
    wcel
    @31
    @70
    @73
    @68
    @73
    @67
    @3
    @67
    cc
    wcel
    #
    @73
    halfcn
    a1i
    @73
    id
    mulcld
    #
    coscld
    #
    3syl
    #
    eqeltrrd
    adantl
    @26
    wph
    @24
    vs
    @0
    c2
    @67
    cmul
    co
    #
    @69
    cmul
    co
    #
    cmpt
    #
    @25
    @24
    cr
    vs
    cr
    @12
    cmpt
    #
    @0
    cres
    #
    cdv
    co
    #
    cr
    @81
    cdv
    co
    #
    @0
    @64
    cnt
    cfv
    cfv
    #
    cres
    #
    @80
    @23
    @82
    cr
    cdv
    @82
    @23
    @0
    cr
    wss
    #
    @82
    @23
    wceq
    cA
    cB
    ioossre
    #
    vs
    cr
    @0
    @12
    resmpt
    ax-mp
    eqcomi
    oveq2i
    cr
    cc
    wss
    #
    cr
    cc
    @81
    wf
    cr
    cr
    wss
    @87
    @83
    @86
    wceq
    ax-resscn
    vs
    cr
    cc
    @12
    @81
    @81
    eqid
    @50
    fmpti
    cr
    ssid
    @88
    cr
    @0
    cr
    @64
    @81
    @62
    @65
    @66
    dvres
    mp4an
    @86
    cr
    vs
    cc
    c2
    @68
    csin
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cr
    cres
    #
    cdv
    co
    #
    @0
    cres
    cc
    @92
    cdv
    co
    #
    cr
    cres
    #
    @0
    cres
    #
    @80
    @84
    @94
    @85
    @0
    @81
    @93
    cr
    cdv
    @93
    vs
    cr
    @91
    cmpt
    #
    @81
    @89
    @93
    @98
    wceq
    ax-resscn
    vs
    cc
    cr
    @91
    resmpt
    ax-mp
    vs
    cr
    @91
    @12
    @30
    @90
    @11
    c2
    cmul
    @30
    @68
    @10
    csin
    @71
    fveq2d
    oveq2d
    mpteq2ia
    eqtr2i
    oveq2i
    cA
    cB
    ioontr
    reseq12i
    @94
    @96
    @0
    @59
    cc
    cc
    @92
    wf
    cc
    cc
    wss
    cr
    @95
    cdm
    #
    wss
    @94
    @96
    wceq
    reelprrecn
    vs
    cc
    cc
    @91
    @92
    @92
    eqid
    @73
    c2
    @90
    @73
    2cnd
    @73
    @68
    @75
    sincld
    mulcld
    fmpti
    cc
    ssid
    cr
    vs
    cc
    @79
    cmpt
    #
    cdm
    #
    @99
    cr
    cc
    @101
    ax-resscn
    @79
    cc
    wcel
    @101
    cc
    wceq
    vs
    cc
    vs
    cc
    @79
    cc
    dmmptg
    @73
    @78
    @69
    @78
    cc
    wcel
    @73
    c2
    @67
    2cn
    halfcn
    mulcli
    a1i
    @76
    mulcld
    mprg
    sseqtr4i
    @95
    @100
    c2
    cc
    wcel
    @74
    @95
    @100
    wceq
    2cn
    halfcn
    vs
    c2
    @67
    dvasinbx
    mp2an
    #
    dmeqi
    sseqtr4i
    cc
    cr
    @92
    dvres3
    mp4an
    reseq1i
    @97
    @100
    cr
    cres
    #
    @0
    cres
    #
    @100
    @0
    cres
    #
    @80
    @96
    @103
    @0
    @95
    @100
    cr
    @102
    reseq1i
    reseq1i
    @87
    @104
    @105
    wceq
    @88
    @100
    @0
    cr
    resabs1
    ax-mp
    @0
    cc
    wss
    @105
    @80
    wceq
    cA
    cB
    ioosscn
    vs
    cc
    @0
    @79
    resmpt
    ax-mp
    3eqtri
    3eqtri
    3eqtri
    vs
    @0
    @79
    @14
    @27
    @79
    c1
    @69
    cmul
    co
    #
    @69
    @14
    @79
    @106
    wceq
    @27
    @78
    c1
    @69
    cmul
    c2
    2cn
    2ne0
    recidi
    oveq1i
    a1i
    @27
    @69
    @77
    mulid2d
    @72
    3eqtrd
    mpteq2ia
    eqtri
    #
    a1i
    dvmptdiv
    eqtrd
    #
    feq1d
    mpbird
    @108
    jca
    @107
    pm3.2i
end
