include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "ccos.mm"
include "cfv.mm"
include "citg.mm"
include "cr.mm"
include "cicc.mm"
include "csin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmin.mm"
include "wcel.mm"
include "wa.mm"
include "cc.mm"
include "wceq.mm"
include "cres.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "iccssred.mm"
include "resmptd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "wss.mm"
include "wf.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "sselda.mm"
include "adantr.mm"
include "simpr.mm"
include "mulcld.mm"
include "sincld.mm"
include "cc0.mm"
include "wne.mm"
include "divcld.mm"
include "syldan.mm"
include "eqid.mm"
include "fmptd.mm"
include "ssid.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "tgioo2.mm"
include "dvres.mm"
include "syl22anc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "coscld.mm"
include "cdm.mm"
include "dvsinax.mm"
include "syl.mm"
include "dmeqd.mm"
include "wral.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "eqtr2d.mm"
include "syl5sseq.mm"
include "dvres3.mm"
include "reseq1d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "dvmptdivc.mm"
include "iccntr.mm"
include "syl2anc.mm"
include "reseq12d.mm"
include "ioossre.mm"
include "resmpt.mm"
include "mp1i.mm"
include "elioore.mm"
include "recnd.mm"
include "sylan2.mm"
include "divcan3d.mm"
include "mpteq2dva.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "syl5ss.mm"
include "fvmptd.mm"
include "itgeq2dv.mm"
include "eqidd.mm"
include "oveq1d.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "ccncf.mm"
include "coscn.mm"
include "constcncfg.mm"
include "idcncfg.mm"
include "mulcncf.mm"
include "cncfmpt1f.mm"
include "eqeltrd.mm"
include "cibl.mm"
include "ioossicc.mm"
include "cvol.mm"
include "ioombl.mm"
include "syl6ss.mm"
include "cniccibl.mm"
include "iblss.mm"
include "sincn.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "neneq.mm"
include "elsni.mm"
include "con3i.mm"
include "3syl.mm"
include "eldifd.mm"
include "difssd.mm"
include "divcncf.mm"
include "ftc2.mm"
include "divsubdird.mm"
include "3eqtr4d.mm"

theorem itgcoscmulx
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vk: setvar k
  assume itgcoscmulx.a: |- ( ph -> A e. CC )
  assume itgcoscmulx.b: |- ( ph -> B e. RR )
  assume itgcoscmulx.c: |- ( ph -> C e. RR )
  assume itgcoscmulx.blec: |- ( ph -> B <_ C )
  assume itgcoscmulx.an0: |- ( ph -> A =/= 0 )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> S. ( B (,) C ) ( cos ` ( A x. x ) ) _d x = ( ( ( sin ` ( A x. C ) ) - ( sin ` ( A x. B ) ) ) / A ) )

  proof
    wph
    vx
    cB
    cC
    cioo
    co
    #
    cA
    vx
    cv
    #
    cmul
    co
    #
    ccos
    cfv
    #
    citg
    vx
    @0
    @1
    cr
    vy
    cB
    cC
    cicc
    co
    #
    cA
    vy
    cv
    #
    cmul
    co
    #
    csin
    cfv
    #
    cA
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    #
    cfv
    #
    citg
    #
    cA
    cC
    cmul
    co
    #
    csin
    cfv
    #
    cA
    cB
    cmul
    co
    #
    csin
    cfv
    #
    cmin
    co
    cA
    cdiv
    co
    #
    wph
    vx
    @0
    @3
    @11
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @11
    @3
    @19
    vy
    @1
    @6
    ccos
    cfv
    #
    @3
    @0
    @10
    cc
    wph
    @10
    vy
    @0
    @20
    cmpt
    #
    wceq
    @18
    wph
    @10
    cr
    vy
    cr
    @8
    cmpt
    #
    @4
    cres
    #
    cdv
    co
    #
    cr
    @22
    cdv
    co
    #
    @4
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
    @21
    wph
    @9
    @23
    cr
    cdv
    wph
    @23
    @9
    wph
    vy
    cr
    @4
    @8
    wph
    cB
    cC
    itgcoscmulx.b
    itgcoscmulx.c
    iccssred
    #
    resmptd
    eqcomd
    oveq2d
    wph
    cr
    cc
    wss
    #
    cr
    cc
    @22
    wf
    cr
    cr
    wss
    #
    @4
    cr
    wss
    @24
    @28
    wceq
    @30
    wph
    ax-resscn
    a1i
    #
    wph
    vy
    cr
    @8
    cc
    @22
    wph
    @5
    cr
    wcel
    #
    @5
    cc
    wcel
    #
    @8
    cc
    wcel
    wph
    cr
    cc
    @5
    @32
    sselda
    #
    wph
    @34
    wa
    #
    @7
    cA
    @36
    @6
    @36
    cA
    @5
    wph
    cA
    cc
    wcel
    #
    @34
    itgcoscmulx.a
    adantr
    #
    wph
    @34
    simpr
    mulcld
    #
    sincld
    #
    @38
    wph
    cA
    cc0
    wne
    #
    @34
    itgcoscmulx.an0
    adantr
    divcld
    syldan
    @22
    eqid
    fmptd
    @31
    wph
    cr
    ssid
    a1i
    @29
    cr
    @4
    cr
    @26
    @22
    ccnfld
    ctopn
    cfv
    #
    @42
    eqid
    #
    @42
    @43
    tgioo2
    dvres
    syl22anc
    wph
    @28
    vy
    cr
    cA
    @20
    cmul
    co
    #
    cA
    cdiv
    co
    #
    cmpt
    #
    @0
    cres
    #
    vy
    @0
    @45
    cmpt
    #
    @21
    wph
    @25
    @46
    @27
    @0
    wph
    vy
    @7
    @44
    cA
    cr
    cc
    cr
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
    wph
    @33
    @34
    @7
    cc
    wcel
    @35
    @40
    syldan
    wph
    @33
    wa
    #
    cA
    @20
    wph
    @37
    @33
    itgcoscmulx.a
    adantr
    #
    @51
    @6
    @51
    cA
    @5
    @52
    @35
    mulcld
    coscld
    mulcld
    wph
    cr
    vy
    cr
    @7
    cmpt
    #
    cdv
    co
    cr
    vy
    cc
    @7
    cmpt
    #
    cr
    cres
    #
    cdv
    co
    #
    vy
    cr
    @44
    cmpt
    #
    wph
    @53
    @55
    cr
    cdv
    wph
    @55
    @53
    wph
    vy
    cc
    cr
    @7
    @32
    resmptd
    eqcomd
    oveq2d
    wph
    @56
    cc
    @54
    cdv
    co
    #
    cr
    cres
    #
    vy
    cc
    @44
    cmpt
    #
    cr
    cres
    @57
    wph
    @49
    cc
    cc
    @54
    wf
    cc
    cc
    wss
    #
    cr
    @58
    cdm
    #
    wss
    @56
    @59
    wceq
    @50
    wph
    vy
    cc
    @7
    cc
    @54
    @40
    @54
    eqid
    fmptd
    @61
    wph
    cc
    ssid
    a1i
    #
    wph
    cc
    cr
    @62
    ax-resscn
    wph
    @62
    @60
    cdm
    #
    cc
    wph
    @58
    @60
    wph
    @37
    @58
    @60
    wceq
    itgcoscmulx.a
    vy
    cA
    dvsinax
    syl
    #
    dmeqd
    wph
    @44
    cc
    wcel
    #
    vy
    cc
    wral
    @64
    cc
    wceq
    wph
    @66
    vy
    cc
    @36
    cA
    @20
    @38
    @36
    @6
    @39
    coscld
    #
    mulcld
    ralrimiva
    vy
    cc
    @44
    cc
    dmmptg
    syl
    eqtr2d
    syl5sseq
    cc
    cr
    @54
    dvres3
    syl22anc
    wph
    @58
    @60
    cr
    @65
    reseq1d
    wph
    vy
    cc
    cr
    @44
    @32
    resmptd
    3eqtrd
    eqtrd
    itgcoscmulx.a
    itgcoscmulx.an0
    dvmptdivc
    wph
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    @27
    @0
    wceq
    itgcoscmulx.b
    itgcoscmulx.c
    cB
    cC
    iccntr
    syl2anc
    reseq12d
    @0
    cr
    wss
    @47
    @48
    wceq
    wph
    cB
    cC
    ioossre
    #
    vy
    cr
    @0
    @45
    resmpt
    mp1i
    wph
    vy
    @0
    @45
    @20
    wph
    @5
    @0
    wcel
    #
    wa
    @20
    cA
    @71
    wph
    @34
    @20
    cc
    wcel
    @71
    @5
    @5
    cB
    cC
    elioore
    recnd
    @67
    sylan2
    wph
    @37
    @71
    itgcoscmulx.a
    adantr
    wph
    @41
    @71
    itgcoscmulx.an0
    adantr
    divcan3d
    mpteq2dva
    3eqtrd
    3eqtrd
    #
    adantr
    @5
    @1
    wceq
    #
    @20
    @3
    wceq
    @19
    @73
    @6
    @2
    ccos
    @5
    @1
    cA
    cmul
    oveq2
    fveq2d
    adantl
    wph
    @18
    simpr
    @19
    @2
    @19
    cA
    @1
    wph
    @37
    @18
    itgcoscmulx.a
    adantr
    wph
    @0
    cc
    @1
    wph
    @0
    cr
    cc
    @70
    @32
    syl5ss
    #
    sselda
    mulcld
    coscld
    fvmptd
    eqcomd
    itgeq2dv
    wph
    cC
    @9
    cfv
    #
    cB
    @9
    cfv
    #
    cmin
    co
    @14
    cA
    cdiv
    co
    #
    @16
    cA
    cdiv
    co
    #
    cmin
    co
    @12
    @17
    wph
    @75
    @77
    @76
    @78
    cmin
    wph
    vy
    cC
    @8
    @77
    @4
    @9
    cc
    wph
    @9
    eqidd
    #
    @5
    cC
    wceq
    #
    @8
    @77
    wceq
    wph
    @80
    @7
    @14
    cA
    cdiv
    @80
    @6
    @13
    csin
    @5
    cC
    cA
    cmul
    oveq2
    fveq2d
    oveq1d
    adantl
    wph
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    cB
    cC
    cle
    wbr
    #
    cC
    @4
    wcel
    wph
    cB
    itgcoscmulx.b
    rexrd
    #
    wph
    cC
    itgcoscmulx.c
    rexrd
    #
    itgcoscmulx.blec
    cB
    cC
    ubicc2
    syl3anc
    wph
    @14
    cA
    wph
    @13
    wph
    cA
    cC
    itgcoscmulx.a
    wph
    cC
    itgcoscmulx.c
    recnd
    mulcld
    sincld
    #
    itgcoscmulx.a
    itgcoscmulx.an0
    divcld
    fvmptd
    wph
    vy
    cB
    @8
    @78
    @4
    @9
    cc
    @79
    @5
    cB
    wceq
    #
    @8
    @78
    wceq
    wph
    @87
    @7
    @16
    cA
    cdiv
    @87
    @6
    @15
    csin
    @5
    cB
    cA
    cmul
    oveq2
    fveq2d
    oveq1d
    adantl
    wph
    @81
    @82
    @83
    cB
    @4
    wcel
    @84
    @85
    itgcoscmulx.blec
    cB
    cC
    lbicc2
    syl3anc
    wph
    @16
    cA
    wph
    @15
    wph
    cA
    cB
    itgcoscmulx.a
    wph
    cB
    itgcoscmulx.b
    recnd
    mulcld
    sincld
    #
    itgcoscmulx.a
    itgcoscmulx.an0
    divcld
    fvmptd
    oveq12d
    wph
    vx
    cB
    cC
    @9
    itgcoscmulx.b
    itgcoscmulx.c
    itgcoscmulx.blec
    wph
    @10
    @21
    @0
    cc
    ccncf
    co
    @72
    wph
    vy
    @6
    ccos
    @0
    ccos
    cc
    cc
    ccncf
    co
    #
    wcel
    wph
    coscn
    a1i
    #
    wph
    vy
    cA
    @5
    @0
    wph
    vy
    @0
    cA
    cc
    @74
    itgcoscmulx.a
    @63
    constcncfg
    wph
    vy
    @0
    cc
    @74
    @63
    idcncfg
    mulcncf
    cncfmpt1f
    eqeltrd
    wph
    @10
    @21
    cibl
    @72
    wph
    vy
    @0
    @4
    @20
    cc
    @0
    @4
    wss
    wph
    cB
    cC
    ioossicc
    a1i
    @0
    cvol
    cdm
    wcel
    wph
    cB
    cC
    ioombl
    a1i
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @92
    cA
    @5
    wph
    @37
    @91
    itgcoscmulx.a
    adantr
    wph
    @4
    cc
    @5
    wph
    @4
    cr
    cc
    @29
    ax-resscn
    syl6ss
    #
    sselda
    mulcld
    coscld
    wph
    @68
    @69
    vy
    @4
    @20
    cmpt
    #
    @4
    cc
    ccncf
    co
    wcel
    @94
    cibl
    wcel
    itgcoscmulx.b
    itgcoscmulx.c
    wph
    vy
    @6
    ccos
    @4
    @90
    wph
    vy
    cA
    @5
    @4
    wph
    vy
    @4
    cA
    cc
    @93
    itgcoscmulx.a
    @63
    constcncfg
    wph
    vy
    @4
    cc
    @93
    @63
    idcncfg
    mulcncf
    #
    cncfmpt1f
    cB
    cC
    @94
    cniccibl
    syl3anc
    iblss
    eqeltrd
    wph
    vy
    @7
    cA
    @4
    wph
    vy
    @6
    csin
    @4
    csin
    @89
    wcel
    wph
    sincn
    a1i
    @95
    cncfmpt1f
    wph
    vy
    @4
    cA
    cc
    cc0
    csn
    #
    cdif
    @93
    wph
    cA
    cc
    @96
    itgcoscmulx.a
    wph
    @41
    cA
    cc0
    wceq
    #
    wn
    cA
    @96
    wcel
    #
    wn
    itgcoscmulx.an0
    cA
    cc0
    neneq
    @98
    @97
    cA
    cc0
    elsni
    con3i
    3syl
    eldifd
    wph
    cc
    @96
    difssd
    constcncfg
    divcncf
    ftc2
    wph
    @14
    @16
    cA
    @86
    @88
    itgcoscmulx.a
    itgcoscmulx.an0
    divsubdird
    3eqtr4d
    eqtrd
end
