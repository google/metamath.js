include "cioo.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "csin.mm"
include "cfv.mm"
include "citg.mm"
include "cr.mm"
include "cicc.mm"
include "ccos.mm"
include "cneg.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmin.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cc.mm"
include "eqid.mm"
include "adantr.mm"
include "simpr.mm"
include "mulcld.mm"
include "coscld.mm"
include "negcld.mm"
include "cc0.mm"
include "wne.mm"
include "divcld.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "sincld.mm"
include "dvcosax.mm"
include "syl.mm"
include "dvmptneg.mm"
include "dvmptdivc.mm"
include "divnegd.mm"
include "eqcomd.mm"
include "divcan3d.mm"
include "negeqd.mm"
include "negnegd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "dvmptresicc.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "ioosscn.mm"
include "sseldi.mm"
include "fvmptd.mm"
include "eqtr2d.mm"
include "itgeq2dv.mm"
include "ccncf.mm"
include "sincn.mm"
include "wss.mm"
include "ssid.mm"
include "constcncfg.mm"
include "idcncfg.mm"
include "mulcncf.mm"
include "cncfmpt1f.mm"
include "eqeltrd.mm"
include "cibl.mm"
include "ioossicc.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "iccssred.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "sselda.mm"
include "cniccibl.mm"
include "syl3anc.mm"
include "iblss.mm"
include "coscn.mm"
include "negcncfg.mm"
include "csn.mm"
include "cdif.mm"
include "neneqd.mm"
include "wb.mm"
include "elsng.mm"
include "mtbird.mm"
include "eldifd.mm"
include "difssd.mm"
include "divcncf.mm"
include "ftc2.mm"
include "caddc.mm"
include "cvv.mm"
include "oveq1d.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "ovexd.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "recnd.mm"
include "oveq2d.mm"
include "subnegd.mm"
include "addcomd.mm"
include "negsubd.mm"
include "divsubdird.mm"

theorem itgsincmulx
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  let vk: setvar k
  assume itgsincmulx.a: |- ( ph -> A e. CC )
  assume itgsincmulx.an0: |- ( ph -> A =/= 0 )
  assume itgsincmulx.b: |- ( ph -> B e. RR )
  assume itgsincmulx.c: |- ( ph -> C e. RR )
  assume itgsincmulx.blec: |- ( ph -> B <_ C )

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
  assert |- ( ph -> S. ( B (,) C ) ( sin ` ( A x. x ) ) _d x = ( ( ( cos ` ( A x. B ) ) - ( cos ` ( A x. C ) ) ) / A ) )

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
    csin
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
    ccos
    cfv
    #
    cneg
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
    cC
    @10
    cfv
    #
    cB
    @10
    cfv
    #
    cmin
    co
    #
    cA
    cB
    cmul
    co
    #
    ccos
    cfv
    #
    cA
    cC
    cmul
    co
    #
    ccos
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
    @12
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @12
    @1
    vy
    @0
    @6
    csin
    cfv
    #
    cmpt
    #
    cfv
    #
    @3
    wph
    @12
    @25
    wceq
    @21
    wph
    @1
    @11
    @24
    wph
    vy
    @9
    @23
    cB
    cC
    vy
    cc
    @9
    cmpt
    #
    @26
    eqid
    wph
    @5
    cc
    wcel
    #
    wa
    #
    @8
    cA
    @28
    @7
    @28
    @6
    @28
    cA
    @5
    wph
    cA
    cc
    wcel
    #
    @27
    itgsincmulx.a
    adantr
    #
    wph
    @27
    simpr
    mulcld
    #
    coscld
    #
    negcld
    #
    @30
    wph
    cA
    cc0
    wne
    @27
    itgsincmulx.an0
    adantr
    #
    divcld
    wph
    cc
    @26
    cdv
    co
    vy
    cc
    cA
    @23
    cneg
    #
    cmul
    co
    #
    cneg
    #
    cA
    cdiv
    co
    #
    cmpt
    vy
    cc
    @23
    cmpt
    wph
    vy
    @8
    @37
    cA
    cc
    cc
    cc
    cc
    cr
    cc
    cpr
    wcel
    wph
    cnelprrecn
    a1i
    #
    @33
    @28
    @36
    @28
    cA
    @35
    @30
    @28
    @23
    @28
    @6
    @31
    sincld
    #
    negcld
    #
    mulcld
    #
    negcld
    wph
    vy
    @7
    @36
    cc
    cc
    cc
    @39
    @32
    @42
    wph
    @29
    cc
    vy
    cc
    @7
    cmpt
    cdv
    co
    vy
    cc
    @36
    cmpt
    wceq
    itgsincmulx.a
    vy
    cA
    dvcosax
    syl
    dvmptneg
    itgsincmulx.a
    itgsincmulx.an0
    dvmptdivc
    wph
    vy
    cc
    @38
    @23
    @28
    @38
    @36
    cA
    cdiv
    co
    #
    cneg
    #
    @35
    cneg
    @23
    @28
    @44
    @38
    @28
    @36
    cA
    @42
    @30
    @34
    divnegd
    eqcomd
    @28
    @43
    @35
    @28
    @35
    cA
    @41
    @30
    @34
    divcan3d
    negeqd
    @28
    @23
    @40
    negnegd
    3eqtrd
    mpteq2dva
    eqtrd
    @40
    itgsincmulx.b
    itgsincmulx.c
    dvmptresicc
    #
    fveq1d
    adantr
    @22
    vy
    @1
    @23
    @3
    @0
    @24
    cc
    @22
    @24
    eqidd
    @5
    @1
    wceq
    #
    @23
    @3
    wceq
    @22
    @46
    @6
    @2
    csin
    @5
    @1
    cA
    cmul
    oveq2
    fveq2d
    adantl
    wph
    @21
    simpr
    #
    @22
    @2
    @22
    cA
    @1
    wph
    @29
    @21
    itgsincmulx.a
    adantr
    @22
    @0
    cc
    @1
    cB
    cC
    ioosscn
    #
    @47
    sseldi
    mulcld
    sincld
    fvmptd
    eqtr2d
    itgeq2dv
    wph
    vx
    cB
    cC
    @10
    itgsincmulx.b
    itgsincmulx.c
    itgsincmulx.blec
    wph
    @11
    @24
    @0
    cc
    ccncf
    co
    @45
    wph
    vy
    @6
    csin
    @0
    csin
    cc
    cc
    ccncf
    co
    #
    wcel
    wph
    sincn
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
    @0
    cc
    wss
    wph
    @48
    a1i
    #
    itgsincmulx.a
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    #
    constcncfg
    wph
    vy
    @0
    cc
    @51
    @52
    idcncfg
    mulcncf
    cncfmpt1f
    eqeltrd
    wph
    @11
    @24
    cibl
    @45
    wph
    vy
    @0
    @4
    @23
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
    @54
    cA
    @5
    wph
    @29
    @53
    itgsincmulx.a
    adantr
    wph
    @4
    cc
    @5
    wph
    @4
    cr
    cc
    wph
    cB
    cC
    itgsincmulx.b
    itgsincmulx.c
    iccssred
    ax-resscn
    syl6ss
    #
    sselda
    mulcld
    sincld
    wph
    cB
    cr
    wcel
    cC
    cr
    wcel
    vy
    @4
    @23
    cmpt
    #
    @4
    cc
    ccncf
    co
    wcel
    @56
    cibl
    wcel
    itgsincmulx.b
    itgsincmulx.c
    wph
    vy
    @6
    csin
    @4
    @50
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
    @55
    itgsincmulx.a
    @52
    constcncfg
    wph
    vy
    @4
    cc
    @55
    @52
    idcncfg
    mulcncf
    #
    cncfmpt1f
    cB
    cC
    @56
    cniccibl
    syl3anc
    iblss
    eqeltrd
    wph
    vy
    @8
    cA
    @4
    wph
    vy
    @4
    @7
    wph
    vy
    @6
    ccos
    @4
    ccos
    @49
    wcel
    wph
    coscn
    a1i
    @57
    cncfmpt1f
    negcncfg
    wph
    vy
    @4
    cA
    cc
    cc0
    csn
    #
    cdif
    @55
    wph
    cA
    cc
    @58
    itgsincmulx.a
    wph
    cA
    @58
    wcel
    #
    cA
    cc0
    wceq
    #
    wph
    cA
    cc0
    itgsincmulx.an0
    neneqd
    wph
    @29
    @59
    @60
    wb
    itgsincmulx.a
    cA
    cc0
    cc
    elsng
    syl
    mtbird
    eldifd
    wph
    cc
    @58
    difssd
    constcncfg
    divcncf
    ftc2
    wph
    @15
    @19
    cneg
    #
    cA
    cdiv
    co
    #
    @17
    cA
    cdiv
    co
    #
    caddc
    co
    #
    @63
    @62
    caddc
    co
    #
    @20
    wph
    @15
    @62
    @17
    cneg
    #
    cA
    cdiv
    co
    #
    cmin
    co
    @62
    @63
    cneg
    #
    cmin
    co
    @64
    wph
    @13
    @62
    @14
    @67
    cmin
    wph
    vy
    cC
    @9
    @62
    @4
    @10
    cvv
    wph
    @10
    eqidd
    #
    @5
    cC
    wceq
    #
    @9
    @62
    wceq
    wph
    @70
    @8
    @61
    cA
    cdiv
    @70
    @7
    @19
    @70
    @6
    @18
    ccos
    @5
    cC
    cA
    cmul
    oveq2
    fveq2d
    negeqd
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
    itgsincmulx.b
    rexrd
    #
    wph
    cC
    itgsincmulx.c
    rexrd
    #
    itgsincmulx.blec
    cB
    cC
    ubicc2
    syl3anc
    wph
    @61
    cA
    cdiv
    ovexd
    fvmptd
    wph
    vy
    cB
    @9
    @67
    @4
    @10
    cvv
    @69
    @5
    cB
    wceq
    #
    @9
    @67
    wceq
    wph
    @76
    @8
    @66
    cA
    cdiv
    @76
    @7
    @17
    @76
    @6
    @16
    ccos
    @5
    cB
    cA
    cmul
    oveq2
    fveq2d
    negeqd
    oveq1d
    adantl
    wph
    @71
    @72
    @73
    cB
    @4
    wcel
    @74
    @75
    itgsincmulx.blec
    cB
    cC
    lbicc2
    syl3anc
    wph
    @66
    cA
    cdiv
    ovexd
    fvmptd
    oveq12d
    wph
    @67
    @68
    @62
    cmin
    wph
    @68
    @67
    wph
    @17
    cA
    wph
    @16
    wph
    cA
    cB
    itgsincmulx.a
    wph
    cB
    itgsincmulx.b
    recnd
    mulcld
    coscld
    #
    itgsincmulx.a
    itgsincmulx.an0
    divnegd
    eqcomd
    oveq2d
    wph
    @62
    @63
    wph
    @61
    cA
    wph
    @19
    wph
    @18
    wph
    cA
    cC
    itgsincmulx.a
    wph
    cC
    itgsincmulx.c
    recnd
    mulcld
    coscld
    #
    negcld
    itgsincmulx.a
    itgsincmulx.an0
    divcld
    #
    wph
    @17
    cA
    @77
    itgsincmulx.a
    itgsincmulx.an0
    divcld
    #
    subnegd
    3eqtrd
    wph
    @62
    @63
    @79
    @80
    addcomd
    wph
    @65
    @63
    @19
    cA
    cdiv
    co
    #
    cneg
    #
    caddc
    co
    @63
    @81
    cmin
    co
    #
    @20
    wph
    @62
    @82
    @63
    caddc
    wph
    @82
    @62
    wph
    @19
    cA
    @78
    itgsincmulx.a
    itgsincmulx.an0
    divnegd
    eqcomd
    oveq2d
    wph
    @63
    @81
    @80
    wph
    @19
    cA
    @78
    itgsincmulx.a
    itgsincmulx.an0
    divcld
    negsubd
    wph
    @20
    @83
    wph
    @17
    @19
    cA
    @77
    @78
    itgsincmulx.a
    itgsincmulx.an0
    divsubdird
    eqcomd
    3eqtrd
    3eqtrd
    3eqtrd
end
