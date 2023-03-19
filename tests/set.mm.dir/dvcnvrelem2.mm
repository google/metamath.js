include "cfv.mm"
include "cnt.mm"
include "wcel.mm"
include "ccnv.mm"
include "ccnp.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "cicc.mm"
include "cima.mm"
include "ctop.mm"
include "cr.mm"
include "wss.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retop.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf1o.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "frn.mm"
include "eqsstr3d.mm"
include "imassrn.mm"
include "syl5sseq.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "ntrss.mm"
include "syl3anc.mm"
include "dvcnvrelem1.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "syl6eleqr.mm"
include "sseldd.mm"
include "cres.mm"
include "crest.mm"
include "wfun.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "ffun.mm"
include "funcnvres.mm"
include "ccn.mm"
include "cc.mm"
include "cdv.mm"
include "cdm.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "cncfss.mm"
include "syl2anc.mm"
include "wf1.mm"
include "f1of1.mm"
include "syl.mm"
include "f1ores.mm"
include "ccmp.mm"
include "wb.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "sstrd.mm"
include "reex.mm"
include "restabs.mm"
include "syl5eq.mm"
include "rpred.mm"
include "resubcld.mm"
include "readdcld.mm"
include "eqid.mm"
include "icccmp.mm"
include "eqeltrrd.mm"
include "syl5ss.mm"
include "rescncf.mm"
include "sylc.mm"
include "cncffvrn.mm"
include "mpbird.mm"
include "cncfcnvcn.mm"
include "mpbid.mm"
include "cncfcn.mm"
include "eleqtrd.mm"
include "cle.mm"
include "wbr.mm"
include "ltsubrpd.mm"
include "ltled.mm"
include "ltaddrpd.mm"
include "w3a.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "wi.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funfvima2.mm"
include "mpd.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "toponuni.mm"
include "cncnpi.mm"
include "ssexg.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleqtrrd.mm"
include "syl5eqel.mm"
include "topontop.mm"
include "sseqtrd.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "difssd.mm"
include "unssd.mm"
include "ssun1.mm"
include "ffvelrnd.mm"
include "elind.mm"
include "restntr.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "feq2d.mm"
include "feq3.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "jca.mm"

theorem dvcnvrelem2
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cT: class T
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assume dvcnvre.f: |- ( ph -> F e. ( X -cn-> RR ) )
  assume dvcnvre.d: |- ( ph -> dom ( RR _D F ) = X )
  assume dvcnvre.z: |- ( ph -> -. 0 e. ran ( RR _D F ) )
  assume dvcnvre.1: |- ( ph -> F : X -1-1-onto-> Y )
  assume dvcnvre.c: |- ( ph -> C e. X )
  assume dvcnvre.r: |- ( ph -> R e. RR+ )
  assume dvcnvre.s: |- ( ph -> ( ( C - R ) [,] ( C + R ) ) C_ X )
  assume dvcnvre.t: |- T = ( topGen ` ran (,) )
  assume dvcnvre.j: |- J = ( TopOpen ` CCfld )
  assume dvcnvre.m: |- M = ( J |`t X )
  assume dvcnvre.n: |- N = ( J |`t Y )


  assert |- ( ph -> ( ( F ` C ) e. ( ( int ` T ) ` Y ) /\ `' F e. ( ( N CnP M ) ` ( F ` C ) ) ) )

  proof
    wph
    cC
    cF
    cfv
    #
    cY
    cT
    cnt
    cfv
    #
    cfv
    #
    wcel
    cF
    ccnv
    #
    @0
    cN
    cM
    ccnp
    co
    cfv
    wcel
    #
    wph
    cF
    cC
    cR
    cmin
    co
    #
    cC
    cR
    caddc
    co
    #
    cicc
    co
    #
    cima
    #
    @1
    cfv
    #
    @2
    @0
    wph
    cT
    ctop
    wcel
    #
    cY
    cr
    wss
    #
    @8
    cY
    wss
    #
    @9
    @2
    wss
    @10
    wph
    cT
    cioo
    crn
    ctg
    cfv
    #
    ctop
    dvcnvre.t
    retop
    eqeltri
    a1i
    #
    wph
    cY
    cF
    crn
    #
    cr
    wph
    cX
    cY
    cF
    wf1o
    #
    cX
    cY
    cF
    wfo
    @15
    cY
    wceq
    dvcnvre.1
    cX
    cY
    cF
    f1ofo
    cX
    cY
    cF
    forn
    3syl
    #
    wph
    cF
    cX
    cr
    ccncf
    co
    wcel
    #
    cX
    cr
    cF
    wf
    #
    @15
    cr
    wss
    dvcnvre.f
    cX
    cr
    cF
    cncff
    #
    cX
    cr
    cF
    frn
    3syl
    #
    eqsstr3d
    #
    wph
    @15
    @8
    cY
    cF
    @7
    imassrn
    #
    @17
    syl5sseq
    #
    cY
    @8
    cT
    cr
    cr
    @13
    cuni
    cT
    cuni
    uniretop
    cT
    @13
    dvcnvre.t
    unieqi
    eqtr4i
    #
    ntrss
    syl3anc
    wph
    @0
    @8
    @13
    cnt
    cfv
    #
    cfv
    @9
    wph
    cC
    cR
    cF
    cX
    cY
    dvcnvre.f
    dvcnvre.d
    dvcnvre.z
    dvcnvre.1
    dvcnvre.c
    dvcnvre.r
    dvcnvre.s
    dvcnvrelem1
    @8
    @1
    @26
    cT
    @13
    cnt
    dvcnvre.t
    fveq2i
    fveq1i
    syl6eleqr
    #
    sseldd
    wph
    @4
    @3
    @8
    cres
    #
    @0
    cN
    @8
    crest
    co
    #
    cM
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    wph
    @28
    @0
    cJ
    @8
    crest
    co
    #
    cM
    ccnp
    co
    #
    cfv
    #
    @31
    wph
    cF
    @7
    cres
    #
    ccnv
    #
    @28
    @35
    wph
    cY
    cX
    @3
    wf
    #
    @3
    wfun
    @37
    @28
    wceq
    wph
    @16
    cY
    cX
    @3
    wf1o
    @38
    dvcnvre.1
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @3
    f1of
    3syl
    #
    cY
    cX
    @3
    ffun
    @7
    cF
    funcnvres
    3syl
    wph
    @37
    @33
    cM
    ccn
    co
    #
    wcel
    @0
    @33
    cuni
    #
    wcel
    @37
    @35
    wcel
    wph
    @37
    @8
    cX
    ccncf
    co
    #
    @40
    wph
    @8
    @7
    ccncf
    co
    #
    @42
    @37
    wph
    @7
    cX
    wss
    #
    cX
    cc
    wss
    #
    @43
    @42
    wss
    dvcnvre.s
    wph
    cX
    cr
    cc
    wph
    cX
    cr
    cF
    cdv
    co
    cdm
    cr
    dvcnvre.d
    cr
    cF
    dvbsss
    syl6eqssr
    #
    ax-resscn
    syl6ss
    #
    @8
    @7
    cX
    cncfss
    syl2anc
    wph
    @7
    @8
    @36
    wf1o
    #
    @37
    @43
    wcel
    #
    wph
    cX
    cY
    cF
    wf1
    #
    @44
    @48
    wph
    @16
    @50
    dvcnvre.1
    cX
    cY
    cF
    f1of1
    syl
    dvcnvre.s
    cX
    cY
    @7
    cF
    f1ores
    syl2anc
    #
    wph
    cJ
    @7
    crest
    co
    #
    ccmp
    wcel
    @36
    @7
    @8
    ccncf
    co
    wcel
    #
    @48
    @49
    wb
    wph
    cT
    @7
    crest
    co
    #
    @52
    ccmp
    wph
    @54
    cJ
    cr
    crest
    co
    #
    @7
    crest
    co
    #
    @52
    cT
    @55
    @7
    crest
    cT
    @13
    @55
    dvcnvre.t
    cJ
    dvcnvre.j
    tgioo2
    eqtri
    #
    oveq1i
    wph
    cJ
    ctop
    wcel
    #
    @7
    cr
    wss
    cr
    cvv
    wcel
    #
    @56
    @52
    wceq
    @58
    wph
    cJ
    dvcnvre.j
    cnfldtop
    a1i
    #
    wph
    @7
    cX
    cr
    dvcnvre.s
    @46
    sstrd
    @59
    wph
    reex
    a1i
    #
    @7
    cr
    cJ
    ctop
    cvv
    restabs
    syl3anc
    syl5eq
    wph
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @54
    ccmp
    wcel
    wph
    cC
    cR
    wph
    cX
    cr
    cC
    @46
    dvcnvre.c
    sseldd
    #
    wph
    cR
    dvcnvre.r
    rpred
    #
    resubcld
    #
    wph
    cC
    cR
    @64
    @65
    readdcld
    #
    @5
    @6
    @54
    cT
    dvcnvre.t
    @54
    eqid
    icccmp
    syl2anc
    eqeltrrd
    wph
    @53
    @7
    @8
    @36
    wf
    #
    wph
    @48
    @68
    @51
    @7
    @8
    @36
    f1of
    syl
    wph
    @8
    cc
    wss
    #
    @36
    @7
    cr
    ccncf
    co
    wcel
    #
    @53
    @68
    wb
    wph
    @8
    @15
    cc
    @23
    wph
    @15
    cr
    cc
    @21
    ax-resscn
    syl6ss
    syl5ss
    #
    wph
    @44
    @18
    @70
    dvcnvre.s
    dvcnvre.f
    cX
    cr
    @7
    cF
    rescncf
    sylc
    @7
    cr
    @8
    @36
    cncffvrn
    syl2anc
    mpbird
    @36
    cJ
    @52
    @7
    @8
    dvcnvre.j
    @52
    eqid
    cncfcnvcn
    syl2anc
    mpbid
    sseldd
    wph
    @69
    @45
    @42
    @40
    wceq
    @71
    @47
    @8
    cX
    cJ
    @33
    cM
    dvcnvre.j
    @33
    eqid
    dvcnvre.m
    cncfcn
    syl2anc
    eleqtrd
    wph
    @0
    @8
    @41
    wph
    cC
    @7
    wcel
    #
    @0
    @8
    wcel
    #
    wph
    @72
    cC
    cr
    wcel
    #
    @5
    cC
    cle
    wbr
    #
    cC
    @6
    cle
    wbr
    #
    @64
    wph
    @5
    cC
    @66
    @64
    wph
    cC
    cR
    @64
    dvcnvre.r
    ltsubrpd
    ltled
    wph
    cC
    @6
    @64
    @67
    wph
    cC
    cR
    @64
    dvcnvre.r
    ltaddrpd
    ltled
    wph
    @62
    @63
    @72
    @74
    @75
    @76
    w3a
    wb
    @66
    @67
    @5
    @6
    cC
    elicc2
    syl2anc
    mpbir3and
    wph
    cF
    wfun
    #
    @7
    cF
    cdm
    #
    wss
    @72
    @73
    wi
    wph
    @18
    @19
    @77
    dvcnvre.f
    @20
    cX
    cr
    cF
    ffun
    3syl
    wph
    @7
    cX
    @78
    dvcnvre.s
    wph
    @18
    @19
    @78
    cX
    wceq
    dvcnvre.f
    @20
    cX
    cr
    cF
    fdm
    3syl
    sseqtr4d
    @7
    cC
    cF
    funfvima2
    syl2anc
    mpd
    wph
    @33
    @8
    ctopon
    cfv
    wcel
    #
    @8
    @41
    wceq
    wph
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    @69
    @79
    cJ
    dvcnvre.j
    cnfldtopon
    #
    @71
    @8
    cJ
    cc
    resttopon
    sylancr
    @8
    @33
    toponuni
    syl
    eleqtrd
    @0
    @37
    @33
    cM
    @41
    @41
    eqid
    cncnpi
    syl2anc
    eqeltrrd
    wph
    @0
    @30
    @34
    wph
    @29
    @33
    cM
    ccnp
    wph
    @29
    cJ
    cY
    crest
    co
    #
    @8
    crest
    co
    #
    @33
    cN
    @82
    @8
    crest
    dvcnvre.n
    oveq1i
    wph
    @58
    @12
    cY
    cvv
    wcel
    #
    @83
    @33
    wceq
    @60
    @24
    wph
    @11
    @59
    @84
    @22
    reex
    cY
    cr
    cvv
    ssexg
    sylancl
    @8
    cY
    cJ
    ctop
    cvv
    restabs
    syl3anc
    syl5eq
    oveq1d
    fveq1d
    eleqtrrd
    wph
    cN
    ctop
    wcel
    #
    @8
    cN
    cuni
    #
    wss
    @0
    @8
    cN
    cnt
    cfv
    #
    cfv
    #
    wcel
    @86
    cM
    cuni
    #
    @3
    wf
    #
    @4
    @32
    wb
    wph
    cN
    cY
    ctopon
    cfv
    #
    wcel
    #
    @85
    wph
    cN
    @82
    @91
    dvcnvre.n
    wph
    @80
    cY
    cc
    wss
    @82
    @91
    wcel
    @81
    wph
    cY
    cr
    cc
    @22
    ax-resscn
    syl6ss
    cY
    cJ
    cc
    resttopon
    sylancr
    syl5eqel
    #
    cY
    cN
    topontop
    syl
    wph
    @8
    cY
    @86
    @24
    wph
    @92
    cY
    @86
    wceq
    @93
    cY
    cN
    toponuni
    syl
    #
    sseqtrd
    wph
    @0
    @8
    cr
    cY
    cdif
    #
    cun
    #
    @1
    cfv
    #
    cY
    cin
    #
    @88
    wph
    @97
    cY
    @0
    wph
    @9
    @97
    @0
    wph
    @10
    @96
    cr
    wss
    @8
    @96
    wss
    #
    @9
    @97
    wss
    @14
    wph
    @8
    @95
    cr
    wph
    @8
    cY
    cr
    @24
    @22
    sstrd
    wph
    cr
    cY
    difssd
    unssd
    @99
    wph
    @8
    @95
    ssun1
    a1i
    @96
    @8
    cT
    cr
    @25
    ntrss
    syl3anc
    @27
    sseldd
    wph
    cX
    cY
    cC
    cF
    wph
    @16
    cX
    cY
    cF
    wf
    dvcnvre.1
    cX
    cY
    cF
    f1of
    syl
    dvcnvre.c
    ffvelrnd
    elind
    wph
    @8
    cT
    cY
    crest
    co
    #
    cnt
    cfv
    #
    cfv
    #
    @98
    @88
    wph
    @10
    @11
    @12
    @102
    @98
    wceq
    @14
    @22
    @24
    @8
    cT
    @100
    cr
    cY
    @25
    @100
    eqid
    restntr
    syl3anc
    wph
    @8
    @101
    @87
    wph
    @100
    cN
    cnt
    wph
    @55
    cY
    crest
    co
    #
    @82
    @100
    cN
    wph
    @58
    @11
    @59
    @103
    @82
    wceq
    @60
    @22
    @61
    cY
    cr
    cJ
    ctop
    cvv
    restabs
    syl3anc
    cT
    @55
    cY
    crest
    @57
    oveq1i
    dvcnvre.n
    3eqtr4g
    fveq2d
    fveq1d
    eqtr3d
    eleqtrd
    wph
    @86
    cX
    @3
    wf
    #
    @90
    wph
    @38
    @104
    @39
    wph
    cY
    @86
    cX
    @3
    @94
    feq2d
    mpbid
    wph
    cM
    cX
    ctopon
    cfv
    #
    wcel
    cX
    @89
    wceq
    @104
    @90
    wb
    wph
    cM
    cJ
    cX
    crest
    co
    #
    @105
    dvcnvre.m
    wph
    @80
    @45
    @106
    @105
    wcel
    @81
    @47
    cX
    cJ
    cc
    resttopon
    sylancr
    syl5eqel
    cX
    cM
    toponuni
    cX
    @89
    @86
    @3
    feq3
    3syl
    mpbid
    @8
    @0
    @3
    cN
    cM
    @86
    @89
    @86
    eqid
    @89
    eqid
    cnprest
    syl22anc
    mpbird
    jca
end
