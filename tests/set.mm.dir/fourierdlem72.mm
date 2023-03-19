include "cr.mm"
include "cdv.mm"
include "co.mm"
include "cmul.mm"
include "cof.mm"
include "cioo.mm"
include "cc.mm"
include "ccncf.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "a1i.mm"
include "caddc.mm"
include "cmin.mm"
include "cdiv.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "elioore.mm"
include "adantl.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "cc0.mm"
include "wne.mm"
include "cicc.mm"
include "wn.mm"
include "ioossicc.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "wb.mm"
include "id.mm"
include "necon1bi.mm"
include "eleq1d.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "condan.mm"
include "redivcld.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "c2.mm"
include "csin.mm"
include "2re.mm"
include "rehalfcld.mm"
include "resincld.mm"
include "remulcld.mm"
include "2cnd.mm"
include "recnd.mm"
include "halfcld.mm"
include "sincld.mm"
include "2ne0.mm"
include "cpi.mm"
include "cneg.mm"
include "sselda.mm"
include "fourierdlem44.mm"
include "syl2anc.mm"
include "mulne0d.mm"
include "feqmptd.mm"
include "offval2.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "subcld.mm"
include "wss.mm"
include "ioossre.mm"
include "divcld.mm"
include "mulcld.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "nelrdva.mm"
include "cres.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "wceq.mm"
include "fssd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "ioontr.mm"
include "reseq2i.mm"
include "syl6eq.mm"
include "c1.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cfz.mm"
include "cmap.mm"
include "clt.mm"
include "cfzo.mm"
include "wral.mm"
include "cn.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "simpld.mm"
include "elmapi.mm"
include "elfzofz.mm"
include "rexrd.mm"
include "fzofzp1.mm"
include "pire.mm"
include "renegcld.mm"
include "fourierdlem13.mm"
include "simprd.mm"
include "eqeltrd.mm"
include "fourierdlem10.mm"
include "leadd2dd.mm"
include "eqbrtrd.mm"
include "breqtrrd.mm"
include "ioossioo.mm"
include "resabs1d.mm"
include "eqcomd.mm"
include "ancli.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "reseq2d.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "rescncf.mm"
include "fourierdlem59.mm"
include "sseldd.mm"
include "iooretop.mm"
include "fourierdlem58.mm"
include "dvmulcncf.mm"

theorem fourierdlem72
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cU: class U
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cH: class H
  let cK: class K
  let cM: class M
  let cO: class O
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem72.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem72.xre: |- ( ph -> X e. RR )
  assume fourierdlem72.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( -u _pi + X ) /\ ( p ` m ) = ( _pi + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem72.m: |- ( ph -> M e. NN )
  assume fourierdlem72.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem72.dvcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( ( RR _D F ) |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) e. ( ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) -cn-> RR ) )
  assume fourierdlem72.a: |- ( ph -> A e. RR )
  assume fourierdlem72.b: |- ( ph -> B e. RR )
  assume fourierdlem72.altb: |- ( ph -> A < B )
  assume fourierdlem72.ab: |- ( ph -> ( A (,) B ) C_ ( -u _pi [,] _pi ) )
  assume fourierdlem72.n0: |- ( ph -> -. 0 e. ( A [,] B ) )
  assume fourierdlem72.c: |- ( ph -> C e. RR )
  assume fourierdlem72.q: |- Q = ( i e. ( 0 ... M ) |-> ( ( V ` i ) - X ) )
  assume fourierdlem72.u: |- ( ph -> U e. ( 0 ..^ M ) )
  assume fourierdlem72.abss: |- ( ph -> ( A (,) B ) C_ ( ( Q ` U ) (,) ( Q ` ( U + 1 ) ) ) )
  assume fourierdlem72.h: |- H = ( s e. ( A (,) B ) |-> ( ( ( F ` ( X + s ) ) - C ) / s ) )
  assume fourierdlem72.k: |- K = ( s e. ( A (,) B ) |-> ( s / ( 2 x. ( sin ` ( s / 2 ) ) ) ) )
  assume fourierdlem72.o: |- O = ( s e. ( A (,) B ) |-> ( ( H ` s ) x. ( K ` s ) ) )

  disjoint A s
  disjoint B s
  disjoint C s
  disjoint F i
  disjoint F s
  disjoint H s
  disjoint K s
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint U i
  disjoint V i
  disjoint V p
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint X s
  disjoint i ph
  disjoint ph s
  disjoint k x
  assert |- ( ph -> ( RR _D O ) e. ( ( A (,) B ) -cn-> CC ) )

  proof
    wph
    cr
    cO
    cdv
    co
    cr
    cH
    cK
    cmul
    cof
    co
    #
    cdv
    co
    cA
    cB
    cioo
    co
    #
    cc
    ccncf
    co
    #
    wph
    cO
    @0
    cr
    cdv
    wph
    @0
    vs
    @1
    vs
    cv
    #
    cH
    cfv
    #
    @3
    cK
    cfv
    #
    cmul
    co
    cmpt
    cO
    wph
    vs
    @1
    @4
    @5
    cmul
    cH
    cK
    cvv
    cr
    cr
    @1
    cvv
    wcel
    wph
    cA
    cB
    cioo
    ovex
    a1i
    wph
    @1
    cr
    @3
    cH
    wph
    vs
    @1
    cX
    @3
    caddc
    co
    #
    cF
    cfv
    #
    cC
    cmin
    co
    #
    @3
    cdiv
    co
    #
    cr
    cH
    wph
    @3
    @1
    wcel
    #
    wa
    #
    @8
    @3
    @11
    @7
    cC
    @11
    cr
    cr
    @6
    cF
    wph
    cr
    cr
    cF
    wf
    @10
    fourierdlem72.f
    adantr
    @11
    cX
    @3
    wph
    cX
    cr
    wcel
    @10
    fourierdlem72.xre
    adantr
    @10
    @3
    cr
    wcel
    wph
    @3
    cA
    cB
    elioore
    adantl
    #
    readdcld
    ffvelrnd
    #
    wph
    cC
    cr
    wcel
    @10
    fourierdlem72.c
    adantr
    resubcld
    @12
    @11
    @3
    cc0
    wne
    #
    cc0
    cA
    cB
    cicc
    co
    #
    wcel
    #
    @11
    @14
    wn
    #
    wa
    @3
    @15
    wcel
    #
    @16
    @10
    @18
    wph
    @17
    @1
    @15
    @3
    cA
    cB
    ioossicc
    sseli
    ad2antlr
    @17
    @18
    @16
    wb
    @11
    @17
    @3
    cc0
    @15
    @14
    @3
    cc0
    @14
    id
    necon1bi
    eleq1d
    adantl
    mpbid
    wph
    @16
    wn
    @10
    @17
    fourierdlem72.n0
    ad2antrr
    condan
    #
    redivcld
    fourierdlem72.h
    fmptd
    #
    ffvelrnda
    wph
    @1
    cr
    @3
    cK
    wph
    vs
    @1
    @3
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
    cdiv
    co
    #
    cr
    cK
    @11
    @3
    @23
    @12
    @11
    c2
    @22
    c2
    cr
    wcel
    @11
    2re
    a1i
    @11
    @21
    @11
    @3
    @12
    rehalfcld
    resincld
    remulcld
    @11
    c2
    @22
    @11
    2cnd
    #
    @11
    @21
    @11
    @3
    @11
    @3
    @12
    recnd
    halfcld
    sincld
    c2
    cc0
    wne
    @11
    2ne0
    a1i
    @11
    @3
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    wcel
    @14
    @22
    cc0
    wne
    wph
    @1
    @27
    @3
    fourierdlem72.ab
    sselda
    @19
    @3
    fourierdlem44
    syl2anc
    mulne0d
    #
    redivcld
    fourierdlem72.k
    fmptd
    #
    ffvelrnda
    wph
    vs
    @1
    cr
    cH
    @20
    feqmptd
    wph
    vs
    @1
    cr
    cK
    @29
    feqmptd
    offval2
    fourierdlem72.o
    syl6reqr
    oveq2d
    wph
    cr
    cH
    cK
    @1
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    wph
    vs
    @1
    @9
    cc
    cH
    @11
    @8
    @3
    @11
    @7
    cC
    @11
    @7
    @13
    recnd
    wph
    cC
    cc
    wcel
    @10
    wph
    cC
    fourierdlem72.c
    recnd
    adantr
    subcld
    @11
    @3
    wph
    @1
    cr
    @3
    @1
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    sselda
    recnd
    #
    @19
    divcld
    fourierdlem72.h
    fmptd
    wph
    vs
    @1
    @24
    cc
    cK
    @11
    @3
    @23
    @30
    @11
    c2
    @22
    @25
    @11
    @21
    @11
    @3
    @30
    halfcld
    sincld
    mulcld
    @28
    divcld
    fourierdlem72.k
    fmptd
    wph
    @1
    cr
    ccncf
    co
    #
    @2
    cr
    cH
    cdv
    co
    wph
    cr
    cc
    wss
    #
    cc
    cc
    wss
    #
    @31
    @2
    wss
    @32
    wph
    ax-resscn
    a1i
    #
    @33
    wph
    cc
    ssid
    a1i
    @1
    cr
    cc
    cncfss
    syl2anc
    #
    wph
    cA
    cB
    cC
    cF
    cH
    cX
    vs
    fourierdlem72.f
    fourierdlem72.xre
    fourierdlem72.a
    fourierdlem72.b
    wph
    vs
    @1
    cc0
    @19
    nelrdva
    #
    wph
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
    cr
    cF
    cdv
    co
    #
    @39
    cres
    #
    @39
    cr
    ccncf
    co
    #
    wph
    @40
    @41
    @39
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
    @42
    wph
    @32
    cr
    cc
    cF
    wf
    cr
    cr
    wss
    #
    @39
    cr
    wss
    #
    @40
    @46
    wceq
    @34
    wph
    cr
    cr
    cc
    cF
    fourierdlem72.f
    @34
    fssd
    @47
    wph
    cr
    ssid
    a1i
    @48
    wph
    @37
    @38
    ioossre
    a1i
    cr
    @39
    cr
    @44
    cF
    ccnfld
    ctopn
    cfv
    #
    @49
    eqid
    #
    @49
    @50
    tgioo2
    dvres
    syl22anc
    @45
    @39
    @41
    @37
    @38
    ioontr
    reseq2i
    syl6eq
    wph
    @42
    @41
    cU
    cV
    cfv
    #
    cU
    c1
    caddc
    co
    #
    cV
    cfv
    #
    cioo
    co
    #
    cres
    #
    @39
    cres
    #
    @43
    wph
    @56
    @42
    wph
    @41
    @39
    @54
    wph
    @51
    cxr
    wcel
    @53
    cxr
    wcel
    @51
    @37
    cle
    wbr
    @38
    @53
    cle
    wbr
    @39
    @54
    wss
    #
    wph
    @51
    wph
    cc0
    cM
    cfz
    co
    #
    cr
    cU
    cV
    wph
    cV
    cr
    @58
    cmap
    co
    wcel
    #
    @58
    cr
    cV
    wf
    wph
    @59
    cc0
    cV
    cfv
    @26
    cX
    caddc
    co
    #
    wceq
    cM
    cV
    cfv
    cpi
    cX
    caddc
    co
    #
    wceq
    wa
    vi
    cv
    #
    cV
    cfv
    #
    @62
    c1
    caddc
    co
    #
    cV
    cfv
    #
    clt
    wbr
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    wa
    #
    wph
    cV
    cM
    cP
    cfv
    wcel
    #
    @59
    @67
    wa
    #
    fourierdlem72.v
    wph
    cM
    cn
    wcel
    @68
    @69
    wb
    fourierdlem72.m
    @60
    @61
    cP
    cV
    vi
    vm
    cM
    vp
    fourierdlem72.p
    fourierdlem2
    syl
    mpbid
    simpld
    cV
    cr
    @58
    elmapi
    syl
    #
    wph
    cU
    @66
    wcel
    #
    cU
    @58
    wcel
    fourierdlem72.u
    cU
    cc0
    cM
    elfzofz
    syl
    #
    ffvelrnd
    #
    rexrd
    wph
    @53
    wph
    @58
    cr
    @52
    cV
    @70
    wph
    @71
    @52
    @58
    wcel
    fourierdlem72.u
    cc0
    cM
    cU
    fzofzp1
    syl
    #
    ffvelrnd
    #
    rexrd
    wph
    @51
    cX
    cU
    cQ
    cfv
    #
    caddc
    co
    #
    @37
    cle
    wph
    @76
    @51
    cX
    cmin
    co
    #
    wceq
    #
    @51
    @77
    wceq
    #
    wph
    @26
    cpi
    cP
    cQ
    vi
    vm
    cU
    cM
    cV
    cX
    vp
    wph
    cpi
    cpi
    cr
    wcel
    wph
    pire
    a1i
    #
    renegcld
    #
    @81
    fourierdlem72.xre
    fourierdlem72.p
    fourierdlem72.m
    fourierdlem72.v
    @72
    fourierdlem72.q
    fourierdlem13
    #
    simprd
    wph
    @76
    cA
    cX
    wph
    @76
    @78
    cr
    wph
    @79
    @80
    @83
    simpld
    wph
    @51
    cX
    @73
    fourierdlem72.xre
    resubcld
    eqeltrd
    #
    fourierdlem72.a
    fourierdlem72.xre
    wph
    @76
    cA
    cle
    wbr
    #
    cB
    @52
    cQ
    cfv
    #
    cle
    wbr
    #
    wph
    @76
    @86
    cA
    cB
    @84
    wph
    @86
    @53
    cX
    cmin
    co
    #
    cr
    wph
    @86
    @88
    wceq
    #
    @53
    cX
    @86
    caddc
    co
    #
    wceq
    #
    wph
    @26
    cpi
    cP
    cQ
    vi
    vm
    @52
    cM
    cV
    cX
    vp
    @82
    @81
    fourierdlem72.xre
    fourierdlem72.p
    fourierdlem72.m
    fourierdlem72.v
    @74
    fourierdlem72.q
    fourierdlem13
    #
    simpld
    wph
    @53
    cX
    @75
    fourierdlem72.xre
    resubcld
    eqeltrd
    #
    fourierdlem72.a
    fourierdlem72.b
    fourierdlem72.altb
    fourierdlem72.abss
    fourierdlem10
    #
    simpld
    leadd2dd
    eqbrtrd
    wph
    @38
    @90
    @53
    cle
    wph
    cB
    @86
    cX
    fourierdlem72.b
    @93
    fourierdlem72.xre
    wph
    @85
    @87
    @94
    simprd
    leadd2dd
    wph
    @89
    @91
    @92
    simprd
    breqtrrd
    @51
    @53
    @37
    @38
    ioossioo
    syl22anc
    #
    resabs1d
    eqcomd
    wph
    @57
    @55
    @54
    cr
    ccncf
    co
    #
    wcel
    #
    @56
    @43
    wcel
    @95
    wph
    @71
    wph
    @71
    wa
    #
    @97
    fourierdlem72.u
    wph
    @71
    fourierdlem72.u
    ancli
    wph
    @62
    @66
    wcel
    #
    wa
    #
    @41
    @63
    @65
    cioo
    co
    #
    cres
    #
    @101
    cr
    ccncf
    co
    #
    wcel
    #
    wi
    @98
    @97
    wi
    vi
    cU
    @66
    @62
    cU
    wceq
    #
    @100
    @98
    @104
    @97
    @105
    @99
    @71
    wph
    @62
    cU
    @66
    eleq1
    anbi2d
    @105
    @102
    @55
    @103
    @96
    @105
    @101
    @54
    @41
    @105
    @63
    @51
    @65
    @53
    cioo
    @62
    cU
    cV
    fveq2
    @105
    @64
    @52
    cV
    @62
    cU
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    #
    reseq2d
    @105
    @101
    @54
    cr
    ccncf
    @106
    oveq1d
    eleq12d
    imbi12d
    fourierdlem72.dvcn
    vtoclg
    sylc
    @54
    cr
    @39
    @55
    rescncf
    sylc
    eqeltrd
    eqeltrd
    fourierdlem72.c
    fourierdlem72.h
    fourierdlem59
    sseldd
    wph
    @31
    @2
    cr
    cK
    cdv
    co
    @35
    wph
    @1
    cK
    vs
    fourierdlem72.k
    fourierdlem72.ab
    @36
    @1
    @44
    wcel
    wph
    cA
    cB
    iooretop
    a1i
    fourierdlem58
    sseldd
    dvmulcncf
    eqeltrd
end
