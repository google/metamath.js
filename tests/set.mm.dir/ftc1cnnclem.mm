include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cv.mm"
include "cabs.mm"
include "cioo.mm"
include "citg.mm"
include "caddc.mm"
include "cmul.mm"
include "cle.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "wi.mm"
include "cicc.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "ltle.mm"
include "imp.mm"
include "ssid.mm"
include "a1i.mm"
include "ioossre.mm"
include "cc.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "ftc1lem1.mm"
include "syldan.mm"
include "cxr.mm"
include "rexrd.mm"
include "w3a.mm"
include "elicc1.mm"
include "biimpa.mm"
include "simp2d.mm"
include "syl21anc.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "ioossioo.mm"
include "syl22anc.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "npcand.mm"
include "itgeq2dv.mm"
include "subcld.mm"
include "cvv.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "fvexd.mm"
include "cmpt.mm"
include "cibl.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "iblss.mm"
include "csn.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "covol.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ioossicc.mm"
include "iccmbl.mm"
include "mblss.mm"
include "iccvolcl.mm"
include "ovolsscl.mm"
include "syl5eqel.mm"
include "iblconst.mm"
include "syl5eqelr.mm"
include "cmbf.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "ctx.mm"
include "ccn.mm"
include "subcn.mm"
include "cres.mm"
include "feqresmpt.mm"
include "rescncf.mm"
include "sylc.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "cncfmptc.mm"
include "mp3an23.mm"
include "cncfmpt2f.mm"
include "cnmbf.mm"
include "sylancr.mm"
include "iblsubnc.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "iblmbf.mm"
include "mbfres.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "itgaddnc.mm"
include "eqtr3d.mm"
include "itgconst.mm"
include "ovolioo.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "ovexd.mm"
include "itgcl.mm"
include "resubcld.mm"
include "recnd.mm"
include "mulcld.mm"
include "cc0.mm"
include "posdifd.mm"
include "gt0ne0d.mm"
include "divdird.mm"
include "divcan4d.mm"
include "divcld.mm"
include "pncand.mm"
include "fveq2d.mm"
include "absdivd.mm"
include "0re.mm"
include "mpd.mm"
include "absidd.mm"
include "abscld.mm"
include "cncfss.mm"
include "mp2an.mm"
include "abscncf.mm"
include "sselii.mm"
include "cncfmpt1f.mm"
include "iblabsnc.mm"
include "itgrecl.mm"
include "rpred.mm"
include "remulcld.mm"
include "ccj.mm"
include "csb.mm"
include "cjcld.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvmpt.mm"
include "mulcncf.mm"
include "itgabsnc.mm"
include "simpr.mm"
include "rpcnd.mm"
include "crp.mm"
include "wral.mm"
include "ralrimiva.mm"
include "sseldi.mm"
include "elioore.mm"
include "adantl.mm"
include "absdifltd.mm"
include "mpbid.mm"
include "simpld.mm"
include "eliooord.mm"
include "lttrd.mm"
include "readdcld.mm"
include "simprd.mm"
include "mpbir2and.mm"
include "weq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "wb.mm"
include "difrp.mm"
include "adantlr.mm"
include "itggt0cn.mm"
include "itgsubnc.mm"
include "mulcomd.mm"
include "breqtrd.mm"
include "biimpar.mm"
include "lelttrd.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem ftc1cnnclem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ftc1cnnc.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1cnnc.a: |- ( ph -> A e. RR )
  assume ftc1cnnc.b: |- ( ph -> B e. RR )
  assume ftc1cnnc.le: |- ( ph -> A <_ B )
  assume ftc1cnnc.f: |- ( ph -> F e. ( ( A (,) B ) -cn-> CC ) )
  assume ftc1cnnc.i: |- ( ph -> F e. L^1 )
  assume ftc1cnnclem.c: |- ( ph -> c e. ( A (,) B ) )
  assume ftc1cnnclem.h: |- H = ( z e. ( ( A [,] B ) \ { c } ) |-> ( ( ( G ` z ) - ( G ` c ) ) / ( z - c ) ) )
  assume ftc1cnnclem.e: |- ( ph -> E e. RR+ )
  assume ftc1cnnclem.r: |- ( ph -> R e. RR+ )
  assume ftc1cnnclem.fc: |- ( ( ph /\ y e. ( A (,) B ) ) -> ( ( abs ` ( y - c ) ) < R -> ( abs ` ( ( F ` y ) - ( F ` c ) ) ) < E ) )
  assume ftc1cnnclem.x1: |- ( ph -> X e. ( A [,] B ) )
  assume ftc1cnnclem.x2: |- ( ph -> ( abs ` ( X - c ) ) < R )
  assume ftc1cnnclem.y1: |- ( ph -> Y e. ( A [,] B ) )
  assume ftc1cnnclem.y2: |- ( ph -> ( abs ` ( Y - c ) ) < R )

  disjoint x z
  disjoint t x
  disjoint X x
  disjoint t z
  disjoint X z
  disjoint X t
  disjoint t y
  disjoint E y
  disjoint E t
  disjoint H y
  disjoint Y x
  disjoint Y t
  disjoint R y
  disjoint x y
  disjoint x z
  disjoint t x
  disjoint A x
  disjoint y z
  disjoint t y
  disjoint A y
  disjoint t z
  disjoint A z
  disjoint A t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B t
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph t
  disjoint G y
  disjoint G z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint c t
  disjoint s x
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint s y
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint s z
  disjoint u z
  disjoint v z
  disjoint w z
  disjoint s t
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint A s
  disjoint u v
  disjoint u w
  disjoint A u
  disjoint v w
  disjoint A v
  disjoint A w
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint c s
  disjoint c u
  disjoint c v
  disjoint c w
  assert |- ( ( ph /\ X < Y ) -> ( abs ` ( ( ( ( G ` Y ) - ( G ` X ) ) / ( Y - X ) ) - ( F ` c ) ) ) < E )

  proof
    wph
    cX
    cY
    clt
    wbr
    #
    wa
    #
    cY
    cG
    cfv
    cX
    cG
    cfv
    cmin
    co
    #
    cY
    cX
    cmin
    co
    #
    cdiv
    co
    #
    vc
    cv
    #
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vt
    cX
    cY
    cioo
    co
    #
    vt
    cv
    #
    cF
    cfv
    #
    @6
    cmin
    co
    #
    citg
    #
    cabs
    cfv
    #
    @3
    cdiv
    co
    #
    cE
    clt
    @1
    @8
    @13
    @3
    cdiv
    co
    #
    cabs
    cfv
    @14
    @3
    cabs
    cfv
    #
    cdiv
    co
    @15
    @1
    @7
    @16
    cabs
    @1
    @7
    @16
    @6
    caddc
    co
    #
    @6
    cmin
    co
    @16
    @1
    @4
    @18
    @6
    cmin
    @1
    @4
    @13
    @6
    @3
    cmul
    co
    #
    caddc
    co
    #
    @3
    cdiv
    co
    @16
    @19
    @3
    cdiv
    co
    #
    caddc
    co
    @18
    @1
    @2
    @20
    @3
    cdiv
    @1
    @2
    vt
    @9
    @11
    citg
    #
    @13
    vt
    @9
    @6
    citg
    #
    caddc
    co
    #
    @20
    wph
    @0
    cX
    cY
    cle
    wbr
    #
    @2
    @22
    wceq
    wph
    @0
    @25
    wph
    cX
    cr
    wcel
    #
    cY
    cr
    wcel
    #
    @0
    @25
    wi
    wph
    cA
    cB
    cicc
    co
    #
    cr
    cX
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @28
    cr
    wss
    ftc1cnnc.a
    ftc1cnnc.b
    cA
    cB
    iccssre
    syl2anc
    #
    ftc1cnnclem.x1
    sseldd
    #
    wph
    @28
    cr
    cY
    @29
    ftc1cnnclem.y1
    sseldd
    #
    cX
    cY
    ltle
    syl2anc
    imp
    #
    wph
    vx
    vt
    cA
    cB
    cA
    cB
    cioo
    co
    #
    cF
    cG
    cX
    cY
    ftc1cnnc.g
    ftc1cnnc.a
    ftc1cnnc.b
    ftc1cnnc.le
    @33
    @33
    wss
    wph
    @33
    ssid
    a1i
    @33
    cr
    wss
    wph
    cA
    cB
    ioossre
    #
    a1i
    ftc1cnnc.i
    wph
    cF
    @33
    cc
    ccncf
    co
    wcel
    #
    @33
    cc
    cF
    wf
    ftc1cnnc.f
    @33
    cc
    cF
    cncff
    syl
    #
    ftc1cnnclem.x1
    ftc1cnnclem.y1
    ftc1lem1
    syldan
    wph
    @22
    @24
    wceq
    @0
    wph
    vt
    @9
    @12
    @6
    caddc
    co
    #
    citg
    @22
    @24
    wph
    vt
    @9
    @37
    @11
    wph
    @10
    @9
    wcel
    #
    wa
    #
    @11
    @6
    wph
    @38
    @10
    @33
    wcel
    #
    @11
    cc
    wcel
    wph
    @9
    @33
    @10
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
    cX
    cle
    wbr
    #
    cY
    cB
    cle
    wbr
    #
    @9
    @33
    wss
    #
    wph
    cA
    ftc1cnnc.a
    rexrd
    #
    wph
    cB
    ftc1cnnc.b
    rexrd
    #
    wph
    @41
    @42
    cX
    @28
    wcel
    #
    @43
    @46
    @47
    ftc1cnnclem.x1
    @41
    @42
    wa
    #
    @48
    wa
    cX
    cxr
    wcel
    #
    @43
    cX
    cB
    cle
    wbr
    #
    @49
    @48
    @50
    @43
    @51
    w3a
    cA
    cB
    cX
    elicc1
    biimpa
    simp2d
    syl21anc
    wph
    @41
    @42
    cY
    @28
    wcel
    @44
    @46
    @47
    ftc1cnnclem.y1
    cA
    cB
    cY
    iccleub
    syl3anc
    cA
    cB
    cX
    cY
    ioossioo
    syl22anc
    #
    sselda
    #
    wph
    @33
    cc
    @10
    cF
    @36
    ffvelrnda
    syldan
    #
    wph
    @6
    cc
    wcel
    #
    @38
    wph
    @33
    cc
    @5
    cF
    @36
    ftc1cnnclem.c
    ffvelrnd
    #
    adantr
    #
    npcand
    #
    itgeq2dv
    wph
    vt
    @9
    @12
    @6
    cc
    @39
    @11
    @6
    @54
    @57
    subcld
    #
    wph
    vt
    @9
    @11
    @6
    cc
    @54
    wph
    vt
    @9
    @33
    @11
    cvv
    @52
    @9
    cvol
    cdm
    #
    wcel
    #
    wph
    cX
    cY
    ioombl
    #
    a1i
    #
    wph
    @40
    wa
    @10
    cF
    fvexd
    wph
    cF
    vt
    @33
    @11
    cmpt
    cibl
    wph
    vt
    @33
    cc
    cF
    @36
    feqmptd
    ftc1cnnc.i
    eqeltrrd
    iblss
    @57
    wph
    vt
    @9
    @6
    cmpt
    #
    @9
    @6
    csn
    cxp
    #
    cibl
    vt
    @9
    @6
    fconstmpt
    wph
    @61
    @9
    cvol
    cfv
    #
    cr
    wcel
    #
    @55
    @65
    cibl
    wcel
    @63
    wph
    @66
    @9
    covol
    cfv
    #
    cr
    @61
    @66
    @68
    wceq
    @62
    @9
    mblvol
    ax-mp
    #
    wph
    @9
    cX
    cY
    cicc
    co
    #
    wss
    #
    @70
    cr
    wss
    #
    @70
    covol
    cfv
    #
    cr
    wcel
    @68
    cr
    wcel
    @71
    wph
    cX
    cY
    ioossicc
    a1i
    wph
    @70
    @60
    wcel
    #
    @72
    wph
    @26
    @27
    @74
    @30
    @31
    cX
    cY
    iccmbl
    syl2anc
    #
    @70
    mblss
    syl
    wph
    @70
    cvol
    cfv
    #
    @73
    cr
    wph
    @74
    @76
    @73
    wceq
    @75
    @70
    mblvol
    syl
    wph
    @26
    @27
    @76
    cr
    wcel
    @30
    @31
    cX
    cY
    iccvolcl
    syl2anc
    eqeltrrd
    @9
    @70
    ovolsscl
    syl3anc
    syl5eqel
    #
    @56
    @9
    @6
    iblconst
    syl3anc
    syl5eqelr
    #
    wph
    @61
    vt
    @9
    @12
    cmpt
    #
    @9
    cc
    ccncf
    co
    #
    wcel
    @79
    cmbf
    wcel
    @62
    wph
    vt
    @11
    @6
    cmin
    ccnfld
    ctopn
    cfv
    #
    @9
    @81
    eqid
    #
    cmin
    @81
    @81
    ctx
    co
    @81
    ccn
    co
    wcel
    wph
    @81
    @82
    subcn
    a1i
    #
    wph
    cF
    @9
    cres
    #
    vt
    @9
    @11
    cmpt
    #
    @80
    wph
    vt
    @33
    cc
    @9
    cF
    @36
    @52
    feqresmpt
    #
    wph
    @45
    @35
    @84
    @80
    wcel
    @52
    ftc1cnnc.f
    @33
    cc
    @9
    cF
    rescncf
    sylc
    eqeltrrd
    wph
    @55
    @64
    @80
    wcel
    #
    @56
    @55
    @9
    cc
    wss
    #
    cc
    cc
    wss
    #
    @87
    @9
    cr
    cc
    cX
    cY
    ioossre
    ax-resscn
    sstri
    #
    cc
    ssid
    #
    vt
    @6
    @9
    cc
    cncfmptc
    mp3an23
    syl
    cncfmpt2f
    #
    @9
    @79
    cnmbf
    sylancr
    iblsubnc
    #
    @57
    @78
    wph
    vt
    @9
    @37
    cmpt
    #
    @84
    cmbf
    wph
    @94
    @85
    @84
    wph
    vt
    @9
    @37
    @11
    @58
    mpteq2dva
    @86
    eqtr4d
    wph
    cF
    cmbf
    wcel
    #
    @61
    @84
    cmbf
    wcel
    wph
    cF
    cibl
    wcel
    @95
    ftc1cnnc.i
    cF
    iblmbf
    syl
    @62
    @9
    cF
    mbfres
    sylancl
    eqeltrd
    itgaddnc
    eqtr3d
    adantr
    @1
    @23
    @19
    @13
    caddc
    @1
    @23
    @6
    @66
    cmul
    co
    #
    @19
    wph
    @23
    @96
    wceq
    #
    @0
    wph
    @61
    @67
    @55
    @97
    @63
    @77
    @56
    vt
    @9
    @6
    itgconst
    syl3anc
    adantr
    @1
    @66
    @3
    @6
    cmul
    @1
    @66
    @68
    @3
    @69
    @1
    @26
    @27
    @25
    @68
    @3
    wceq
    wph
    @26
    @0
    @30
    adantr
    wph
    @27
    @0
    @31
    adantr
    @32
    cX
    cY
    ovolioo
    syl3anc
    syl5eq
    #
    oveq2d
    eqtrd
    oveq2d
    3eqtrd
    oveq1d
    @1
    @13
    @19
    @3
    wph
    @13
    cc
    wcel
    @0
    wph
    vt
    @9
    @12
    cvv
    @39
    @11
    @6
    cmin
    ovexd
    #
    @93
    itgcl
    #
    adantr
    #
    @1
    @6
    @3
    wph
    @55
    @0
    @56
    adantr
    #
    wph
    @3
    cc
    wcel
    @0
    wph
    @3
    wph
    cY
    cX
    @31
    @30
    resubcld
    #
    recnd
    #
    adantr
    #
    mulcld
    @105
    @1
    @3
    wph
    @0
    cc0
    @3
    clt
    wbr
    #
    wph
    cX
    cY
    @30
    @31
    posdifd
    biimpa
    #
    gt0ne0d
    #
    divdird
    @1
    @21
    @6
    @16
    caddc
    @1
    @6
    @3
    @102
    @105
    @108
    divcan4d
    oveq2d
    3eqtrd
    oveq1d
    @1
    @16
    @6
    @1
    @13
    @3
    @101
    @105
    @108
    divcld
    @102
    pncand
    eqtrd
    fveq2d
    @1
    @13
    @3
    @101
    @105
    @108
    absdivd
    @1
    @17
    @3
    @14
    cdiv
    @1
    @3
    wph
    @3
    cr
    wcel
    #
    @0
    @103
    adantr
    #
    @1
    @106
    cc0
    @3
    cle
    wbr
    #
    @107
    @1
    cc0
    cr
    wcel
    @109
    @106
    @111
    wi
    0re
    @110
    cc0
    @3
    ltle
    sylancr
    mpd
    absidd
    oveq2d
    3eqtrd
    @1
    @15
    cE
    clt
    wbr
    #
    @14
    @3
    cE
    cmul
    co
    #
    clt
    wbr
    #
    @1
    @14
    vt
    @9
    @12
    cabs
    cfv
    #
    citg
    #
    @113
    @1
    @13
    @101
    abscld
    #
    wph
    @116
    cr
    wcel
    @0
    wph
    vt
    @9
    @115
    @39
    @12
    @59
    abscld
    #
    wph
    vt
    @9
    @12
    cvv
    @99
    @93
    wph
    @61
    vt
    @9
    @115
    cmpt
    #
    @80
    wcel
    @119
    cmbf
    wcel
    @62
    wph
    vt
    @12
    cabs
    @9
    cabs
    cc
    cc
    ccncf
    co
    #
    wcel
    wph
    cc
    cr
    ccncf
    co
    #
    @120
    cabs
    cr
    cc
    wss
    @89
    @121
    @120
    wss
    ax-resscn
    @91
    cc
    cr
    cc
    cncfss
    mp2an
    abscncf
    sselii
    a1i
    @92
    cncfmpt1f
    #
    @9
    @119
    cnmbf
    sylancr
    #
    iblabsnc
    #
    itgrecl
    #
    adantr
    wph
    @113
    cr
    wcel
    @0
    wph
    @3
    cE
    @103
    wph
    cE
    ftc1cnnclem.e
    rpred
    #
    remulcld
    #
    adantr
    wph
    @14
    @116
    cle
    wbr
    @0
    wph
    vt
    vx
    @9
    @12
    cc
    @59
    @93
    @123
    wph
    @61
    vx
    @9
    @13
    ccj
    cfv
    #
    vt
    vx
    cv
    #
    @12
    csb
    #
    cmul
    co
    cmpt
    #
    @80
    wcel
    @131
    cmbf
    wcel
    @62
    wph
    vx
    @128
    @130
    @9
    wph
    @128
    cc
    wcel
    #
    vx
    @9
    @128
    cmpt
    @80
    wcel
    #
    wph
    @13
    @100
    cjcld
    @132
    @88
    @89
    @133
    @90
    @91
    vx
    @128
    @9
    cc
    cncfmptc
    mp3an23
    syl
    wph
    vx
    @9
    @130
    cmpt
    @79
    @80
    vt
    vx
    @9
    @12
    @130
    vx
    @12
    nfcv
    vt
    @129
    @12
    nfcsb1v
    vt
    @129
    @12
    csbeq1a
    cbvmpt
    @92
    syl5eqelr
    mulcncf
    @9
    @131
    cnmbf
    sylancr
    itgabsnc
    adantr
    wph
    @0
    cc0
    @113
    @116
    cmin
    co
    #
    clt
    wbr
    #
    @116
    @113
    clt
    wbr
    #
    @1
    cc0
    vt
    @9
    cE
    @115
    cmin
    co
    #
    citg
    #
    @134
    clt
    @1
    vt
    @137
    cX
    cY
    wph
    @0
    simpr
    wph
    vt
    @9
    @137
    cmpt
    #
    cibl
    wcel
    @0
    wph
    vt
    @9
    cE
    @115
    cr
    wph
    cE
    cr
    wcel
    #
    @38
    @126
    adantr
    #
    wph
    vt
    @9
    cE
    cmpt
    #
    @9
    cE
    csn
    cxp
    #
    cibl
    vt
    @9
    cE
    fconstmpt
    wph
    @61
    @67
    cE
    cc
    wcel
    #
    @143
    cibl
    wcel
    @63
    @77
    wph
    cE
    ftc1cnnclem.e
    rpcnd
    #
    @9
    cE
    iblconst
    syl3anc
    syl5eqelr
    #
    @118
    @124
    wph
    @61
    @139
    @80
    wcel
    #
    @139
    cmbf
    wcel
    @62
    wph
    vt
    cE
    @115
    cmin
    @81
    @9
    @82
    @83
    wph
    @144
    @142
    @80
    wcel
    #
    @145
    @144
    @88
    @89
    @148
    @90
    @91
    vt
    cE
    @9
    cc
    cncfmptc
    mp3an23
    syl
    @122
    cncfmpt2f
    #
    @9
    @139
    cnmbf
    sylancr
    #
    iblsubnc
    adantr
    wph
    @38
    @137
    crp
    wcel
    #
    @0
    @39
    @115
    cE
    clt
    wbr
    #
    @151
    @39
    @40
    vy
    cv
    #
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    @153
    cF
    cfv
    #
    @6
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    wi
    #
    vy
    @33
    wral
    #
    @10
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    @152
    @53
    wph
    @162
    @38
    wph
    @161
    vy
    @33
    ftc1cnnclem.fc
    ralrimiva
    adantr
    @39
    @165
    @5
    cR
    cmin
    co
    #
    @10
    clt
    wbr
    @10
    @5
    cR
    caddc
    co
    #
    clt
    wbr
    @39
    @166
    cX
    @10
    wph
    @166
    cr
    wcel
    @38
    wph
    @5
    cR
    wph
    @33
    cr
    @5
    @34
    ftc1cnnclem.c
    sseldi
    #
    wph
    cR
    ftc1cnnclem.r
    rpred
    #
    resubcld
    adantr
    wph
    @26
    @38
    @30
    adantr
    @38
    @10
    cr
    wcel
    wph
    @10
    cX
    cY
    elioore
    adantl
    #
    wph
    @166
    cX
    clt
    wbr
    #
    @38
    wph
    @171
    cX
    @167
    clt
    wbr
    #
    wph
    cX
    @5
    cmin
    co
    cabs
    cfv
    cR
    clt
    wbr
    @171
    @172
    wa
    ftc1cnnclem.x2
    wph
    cX
    @5
    cR
    @30
    @168
    @169
    absdifltd
    mpbid
    simpld
    adantr
    @39
    cX
    @10
    clt
    wbr
    #
    @10
    cY
    clt
    wbr
    #
    @38
    @173
    @174
    wa
    wph
    @10
    cX
    cY
    eliooord
    adantl
    #
    simpld
    lttrd
    @39
    @10
    cY
    @167
    @170
    wph
    @27
    @38
    @31
    adantr
    wph
    @167
    cr
    wcel
    @38
    wph
    @5
    cR
    @168
    @169
    readdcld
    adantr
    @39
    @173
    @174
    @175
    simprd
    wph
    cY
    @167
    clt
    wbr
    #
    @38
    wph
    @166
    cY
    clt
    wbr
    #
    @176
    wph
    cY
    @5
    cmin
    co
    cabs
    cfv
    cR
    clt
    wbr
    @177
    @176
    wa
    ftc1cnnclem.y2
    wph
    cY
    @5
    cR
    @31
    @168
    @169
    absdifltd
    mpbid
    simprd
    adantr
    lttrd
    @39
    @10
    @5
    cR
    @170
    wph
    @5
    cr
    wcel
    @38
    @168
    adantr
    wph
    cR
    cr
    wcel
    @38
    @169
    adantr
    absdifltd
    mpbir2and
    @161
    @165
    @152
    wi
    vy
    @10
    @33
    vy
    vt
    weq
    #
    @156
    @165
    @160
    @152
    @178
    @155
    @164
    cR
    clt
    @178
    @154
    @163
    cabs
    @153
    @10
    @5
    cmin
    oveq1
    fveq2d
    breq1d
    @178
    @159
    @115
    cE
    clt
    @178
    @158
    @12
    cabs
    @178
    @157
    @11
    @6
    cmin
    @153
    @10
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl3c
    @39
    @115
    cr
    wcel
    @140
    @152
    @151
    wb
    @118
    @141
    @115
    cE
    difrp
    syl2anc
    mpbid
    adantlr
    wph
    @147
    @0
    @149
    adantr
    itggt0cn
    @1
    @138
    vt
    @9
    cE
    citg
    #
    @116
    cmin
    co
    #
    @134
    wph
    @138
    @180
    wceq
    @0
    wph
    vt
    @9
    cE
    @115
    cr
    @141
    @146
    @118
    @124
    @150
    itgsubnc
    adantr
    @1
    @179
    @113
    @116
    cmin
    @1
    @179
    cE
    @66
    cmul
    co
    #
    cE
    @3
    cmul
    co
    #
    @113
    wph
    @179
    @181
    wceq
    #
    @0
    wph
    @61
    @67
    @144
    @183
    @63
    @77
    @145
    vt
    @9
    cE
    itgconst
    syl3anc
    adantr
    @1
    @66
    @3
    cE
    cmul
    @98
    oveq2d
    wph
    @182
    @113
    wceq
    @0
    wph
    cE
    @3
    @145
    @104
    mulcomd
    adantr
    3eqtrd
    oveq1d
    eqtrd
    breqtrd
    wph
    @136
    @135
    wph
    @116
    @113
    @125
    @127
    posdifd
    biimpar
    syldan
    lelttrd
    @1
    @14
    cr
    wcel
    @140
    @109
    @106
    @112
    @114
    wb
    @117
    wph
    @140
    @0
    @126
    adantr
    @110
    @107
    @14
    cE
    @3
    ltdivmul
    syl112anc
    mpbird
    eqbrtrd
end
