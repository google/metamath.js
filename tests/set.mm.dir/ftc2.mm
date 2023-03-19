include "cfv.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "citg.mm"
include "cmin.mm"
include "caddc.mm"
include "cneg.mm"
include "cicc.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "wcel.mm"
include "wceq.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "fvex.mm"
include "fvconst2.mm"
include "syl.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "subcn.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "ioossre.mm"
include "cc.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "ftc1a.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "cncfmpt2f.mm"
include "cc0.mm"
include "crn.mm"
include "ctg.mm"
include "ax-resscn.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "wa.mm"
include "cvv.mm"
include "adantr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "biimpa.mm"
include "simp3d.mm"
include "iooss2.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "cibl.mm"
include "iblss.mm"
include "itgcl.mm"
include "ffvelrnda.mm"
include "subcld.mm"
include "tgioo2.mm"
include "cnt.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sylan2.mm"
include "ftc1cn.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "dvmptsub.mm"
include "subidd.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "dveq0.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "itgeq1.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "lbicc2.mm"
include "c0.mm"
include "iooid.mm"
include "syl6eq.mm"
include "itg0.mm"
include "df-neg.mm"
include "negex.mm"
include "ffvelrnd.mm"
include "pncan3d.mm"
include "negsubd.mm"

theorem ftc2
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  assume ftc2.a: |- ( ph -> A e. RR )
  assume ftc2.b: |- ( ph -> B e. RR )
  assume ftc2.le: |- ( ph -> A <_ B )
  assume ftc2.c: |- ( ph -> ( RR _D F ) e. ( ( A (,) B ) -cn-> CC ) )
  assume ftc2.i: |- ( ph -> ( RR _D F ) e. L^1 )
  assume ftc2.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> CC ) )

  disjoint A t
  disjoint B t
  disjoint F t
  disjoint ph t
  disjoint t x
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint ph x
  assert |- ( ph -> S. ( A (,) B ) ( ( RR _D F ) ` t ) _d t = ( ( F ` B ) - ( F ` A ) ) )

  proof
    wph
    cB
    cF
    cfv
    #
    vt
    cA
    cB
    cioo
    co
    #
    vt
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    citg
    #
    @0
    cmin
    co
    #
    caddc
    co
    @0
    cA
    cF
    cfv
    #
    cneg
    #
    caddc
    co
    @5
    @0
    @7
    cmin
    co
    wph
    @6
    @8
    @0
    caddc
    wph
    cB
    cA
    cB
    cicc
    co
    #
    cA
    vx
    @9
    vt
    cA
    vx
    cv
    #
    cioo
    co
    #
    @4
    citg
    #
    @10
    cF
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    csn
    cxp
    #
    cfv
    #
    @16
    @6
    @8
    wph
    cB
    @9
    wcel
    #
    @18
    @16
    wceq
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @19
    wph
    cA
    ftc2.a
    rexrd
    #
    wph
    cB
    ftc2.b
    rexrd
    #
    ftc2.le
    cA
    cB
    ubicc2
    syl3anc
    #
    @9
    @16
    cB
    cA
    @15
    fvex
    fvconst2
    syl
    wph
    cB
    @15
    cfv
    #
    @18
    @6
    wph
    cB
    @15
    @17
    wph
    cA
    cB
    @15
    ftc2.a
    ftc2.b
    wph
    vx
    @12
    @13
    cmin
    ccnfld
    ctopn
    cfv
    #
    @9
    @27
    eqid
    #
    cmin
    @27
    @27
    ctx
    co
    @27
    ccn
    co
    wcel
    wph
    @27
    @28
    subcn
    a1i
    wph
    vx
    vt
    cA
    cB
    @1
    @3
    vx
    @9
    @12
    cmpt
    #
    @29
    eqid
    #
    ftc2.a
    ftc2.b
    ftc2.le
    @1
    @1
    wss
    wph
    @1
    ssid
    a1i
    @1
    cr
    wss
    wph
    cA
    cB
    ioossre
    a1i
    ftc2.i
    wph
    @3
    @1
    cc
    ccncf
    co
    wcel
    @1
    cc
    @3
    wf
    ftc2.c
    @1
    cc
    @3
    cncff
    syl
    #
    ftc1a
    wph
    cF
    vx
    @9
    @13
    cmpt
    #
    @9
    cc
    ccncf
    co
    #
    wph
    vx
    @9
    cc
    cF
    wph
    cF
    @33
    wcel
    @9
    cc
    cF
    wf
    ftc2.f
    @9
    cc
    cF
    cncff
    syl
    #
    feqmptd
    #
    ftc2.f
    eqeltrrd
    cncfmpt2f
    wph
    cr
    @15
    cdv
    co
    #
    vx
    @1
    cc0
    cmpt
    #
    @1
    cc0
    csn
    cxp
    wph
    @36
    cr
    vx
    @1
    @14
    cmpt
    cdv
    co
    vx
    @1
    @10
    @3
    cfv
    #
    @38
    cmin
    co
    #
    cmpt
    @37
    wph
    vx
    @14
    cr
    cioo
    crn
    ctg
    cfv
    #
    @27
    @9
    @1
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    #
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @9
    cr
    wss
    ftc2.a
    ftc2.b
    cA
    cB
    iccssre
    syl2anc
    #
    wph
    @10
    @9
    wcel
    #
    wa
    #
    @12
    @13
    @46
    vt
    @11
    @4
    cvv
    @4
    cvv
    wcel
    #
    @46
    @2
    @11
    wcel
    wa
    @2
    @3
    fvex
    #
    a1i
    @46
    vt
    @11
    @1
    @4
    cvv
    @46
    @21
    @10
    cB
    cle
    wbr
    #
    @11
    @1
    wss
    @46
    cB
    wph
    @43
    @45
    ftc2.b
    adantr
    rexrd
    @46
    @10
    cr
    wcel
    #
    cA
    @10
    cle
    wbr
    #
    @49
    wph
    @45
    @50
    @51
    @49
    w3a
    #
    wph
    @42
    @43
    @45
    @52
    wb
    ftc2.a
    ftc2.b
    cA
    cB
    @10
    elicc2
    syl2anc
    biimpa
    simp3d
    cA
    @10
    cB
    iooss2
    syl2anc
    @11
    cvol
    cdm
    wcel
    @46
    cA
    @10
    ioombl
    a1i
    @47
    @46
    @2
    @1
    wcel
    #
    wa
    @48
    a1i
    wph
    vt
    @1
    @4
    cmpt
    #
    cibl
    wcel
    @45
    wph
    @3
    @54
    cibl
    wph
    vt
    @1
    cc
    @3
    @31
    feqmptd
    ftc2.i
    eqeltrrd
    #
    adantr
    iblss
    itgcl
    #
    wph
    @9
    cc
    @10
    cF
    @34
    ffvelrnda
    #
    subcld
    @27
    @28
    tgioo2
    #
    @28
    wph
    @42
    @43
    @9
    @40
    cnt
    cfv
    cfv
    @1
    wceq
    ftc2.a
    ftc2.b
    cA
    cB
    iccntr
    syl2anc
    #
    dvmptntr
    wph
    vx
    @12
    @38
    @13
    @38
    cr
    cc
    cc
    @1
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    @10
    @1
    wcel
    #
    wph
    @45
    @12
    cc
    wcel
    @1
    @9
    @10
    cA
    cB
    ioossicc
    sseli
    #
    @56
    sylan2
    wph
    @1
    cc
    @10
    @3
    @31
    ffvelrnda
    #
    wph
    cr
    @29
    cdv
    co
    @3
    cr
    vx
    @1
    @12
    cmpt
    cdv
    co
    vx
    @1
    @38
    cmpt
    #
    wph
    vx
    vt
    cA
    cB
    @3
    @29
    @30
    ftc2.a
    ftc2.b
    ftc2.le
    ftc2.c
    ftc2.i
    ftc1cn
    wph
    vx
    @12
    cr
    @40
    @27
    @9
    @1
    @41
    @44
    @56
    @58
    @28
    @59
    dvmptntr
    wph
    vx
    @1
    cc
    @3
    @31
    feqmptd
    #
    3eqtr3d
    @60
    wph
    @45
    @13
    cc
    wcel
    @61
    @57
    sylan2
    @62
    wph
    cr
    @32
    cdv
    co
    #
    cr
    vx
    @1
    @13
    cmpt
    cdv
    co
    @63
    wph
    vx
    @13
    cr
    @40
    @27
    @9
    @1
    @41
    @44
    @57
    @58
    @28
    @59
    dvmptntr
    wph
    @3
    @65
    @63
    wph
    cF
    @32
    cr
    cdv
    @35
    oveq2d
    @64
    eqtr3d
    eqtr3d
    dvmptsub
    wph
    vx
    @1
    @39
    cc0
    wph
    @60
    wa
    @38
    @62
    subidd
    mpteq2dva
    3eqtrd
    vx
    @1
    cc0
    fconstmpt
    syl6eqr
    dveq0
    fveq1d
    wph
    @19
    @26
    @6
    wceq
    @25
    vx
    cB
    @14
    @6
    @9
    @15
    @10
    cB
    wceq
    #
    @12
    @5
    @13
    @0
    cmin
    @66
    @11
    @1
    wceq
    @12
    @5
    wceq
    @10
    cB
    cA
    cioo
    oveq2
    vt
    @11
    @1
    @4
    itgeq1
    syl
    @10
    cB
    cF
    fveq2
    oveq12d
    @15
    eqid
    #
    @5
    @0
    cmin
    ovex
    fvmpt
    syl
    eqtr3d
    wph
    cA
    @9
    wcel
    #
    @16
    @8
    wceq
    wph
    @20
    @21
    @22
    @68
    @23
    @24
    ftc2.le
    cA
    cB
    lbicc2
    syl3anc
    #
    vx
    cA
    @14
    @8
    @9
    @15
    @10
    cA
    wceq
    #
    @14
    cc0
    @7
    cmin
    co
    @8
    @70
    @12
    cc0
    @13
    @7
    cmin
    @70
    @12
    vt
    c0
    @4
    citg
    #
    cc0
    @70
    @11
    c0
    wceq
    @12
    @71
    wceq
    @70
    @11
    cA
    cA
    cioo
    co
    c0
    @10
    cA
    cA
    cioo
    oveq2
    cA
    iooid
    syl6eq
    vt
    @11
    c0
    @4
    itgeq1
    syl
    vt
    @4
    itg0
    syl6eq
    @10
    cA
    cF
    fveq2
    oveq12d
    @7
    df-neg
    syl6eqr
    @67
    @7
    negex
    fvmpt
    syl
    3eqtr3d
    oveq2d
    wph
    @0
    @5
    wph
    @9
    cc
    cB
    cF
    @34
    @25
    ffvelrnd
    #
    wph
    vt
    @1
    @4
    cvv
    @47
    wph
    @53
    wa
    @48
    a1i
    @55
    itgcl
    pncan3d
    wph
    @0
    @7
    @72
    wph
    @9
    cc
    cA
    cF
    @34
    @69
    ffvelrnd
    negsubd
    3eqtr3d
end
