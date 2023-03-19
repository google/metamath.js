include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cabs.mm"
include "cioo.mm"
include "cv.mm"
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
include "ftc1lem3.mm"
include "ftc1lem1.mm"
include "syldan.mm"
include "cc.mm"
include "cxr.mm"
include "rexrd.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "mpbid.mm"
include "simp2d.mm"
include "iooss1.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sstrd.mm"
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
include "a1i.mm"
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
include "syl.mm"
include "iccvolcl.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "iblconst.mm"
include "syl5eqelr.mm"
include "iblsub.mm"
include "itgadd.mm"
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
include "biimpa.mm"
include "gt0ne0d.mm"
include "divdird.mm"
include "divcan4d.mm"
include "divcld.mm"
include "pncand.mm"
include "fveq2d.mm"
include "absdivd.mm"
include "0re.mm"
include "sylancr.mm"
include "mpd.mm"
include "absidd.mm"
include "abscld.mm"
include "iblabs.mm"
include "itgrecl.mm"
include "rpred.mm"
include "remulcld.mm"
include "itgabs.mm"
include "breqtrrd.mm"
include "crp.mm"
include "wral.mm"
include "ralrimiva.mm"
include "absdifltd.mm"
include "simpld.mm"
include "eliooord.mm"
include "adantl.mm"
include "lttrd.mm"
include "readdcld.mm"
include "simprd.mm"
include "mpbir2and.mm"
include "oveq1.mm"
include "breq1d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "difrp.mm"
include "adantlr.mm"
include "itggt0.mm"
include "itgsub.mm"
include "mulcomd.mm"
include "breqtrd.mm"
include "biimpar.mm"
include "lelttrd.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem ftc1lem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  assume ftc1.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1.a: |- ( ph -> A e. RR )
  assume ftc1.b: |- ( ph -> B e. RR )
  assume ftc1.le: |- ( ph -> A <_ B )
  assume ftc1.s: |- ( ph -> ( A (,) B ) C_ D )
  assume ftc1.d: |- ( ph -> D C_ RR )
  assume ftc1.i: |- ( ph -> F e. L^1 )
  assume ftc1.c: |- ( ph -> C e. ( A (,) B ) )
  assume ftc1.f: |- ( ph -> F e. ( ( K CnP L ) ` C ) )
  assume ftc1.j: |- J = ( L |`t RR )
  assume ftc1.k: |- K = ( L |`t D )
  assume ftc1.l: |- L = ( TopOpen ` CCfld )
  assume ftc1.h: |- H = ( z e. ( ( A [,] B ) \ { C } ) |-> ( ( ( G ` z ) - ( G ` C ) ) / ( z - C ) ) )
  assume ftc1.e: |- ( ph -> E e. RR+ )
  assume ftc1.r: |- ( ph -> R e. RR+ )
  assume ftc1.fc: |- ( ( ph /\ y e. D ) -> ( ( abs ` ( y - C ) ) < R -> ( abs ` ( ( F ` y ) - ( F ` C ) ) ) < E ) )
  assume ftc1.x1: |- ( ph -> X e. ( A [,] B ) )
  assume ftc1.x2: |- ( ph -> ( abs ` ( X - C ) ) < R )
  assume ftc1.y1: |- ( ph -> Y e. ( A [,] B ) )
  assume ftc1.y2: |- ( ph -> ( abs ` ( Y - C ) ) < R )

  disjoint t x
  disjoint t y
  disjoint t z
  disjoint C t
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint G y
  disjoint G z
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint E t
  disjoint E y
  disjoint H y
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Y t
  disjoint Y x
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint R y
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint C u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint D s
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint d e
  disjoint G d
  disjoint e r
  disjoint e s
  disjoint e u
  disjoint e y
  disjoint e z
  disjoint G e
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint A d
  disjoint e t
  disjoint e v
  disjoint e w
  disjoint e x
  disjoint A e
  disjoint A r
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint B d
  disjoint B e
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint d ph
  disjoint e ph
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint F d
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint L s
  disjoint L u
  disjoint L v
  disjoint L w
  assert |- ( ( ph /\ X < Y ) -> ( abs ` ( ( ( ( G ` Y ) - ( G ` X ) ) / ( Y - X ) ) - ( F ` C ) ) ) < E )

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
    @5
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
    @7
    @12
    @3
    cdiv
    co
    #
    cabs
    cfv
    @13
    @3
    cabs
    cfv
    #
    cdiv
    co
    @14
    @1
    @6
    @15
    cabs
    @1
    @6
    @15
    @5
    caddc
    co
    #
    @5
    cmin
    co
    @15
    @1
    @4
    @17
    @5
    cmin
    @1
    @4
    @12
    @5
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
    @15
    @18
    @3
    cdiv
    co
    #
    caddc
    co
    @17
    @1
    @2
    @19
    @3
    cdiv
    @1
    @2
    vt
    @8
    @10
    citg
    #
    @12
    vt
    @8
    @5
    citg
    #
    caddc
    co
    #
    @19
    wph
    @0
    cX
    cY
    cle
    wbr
    #
    @2
    @21
    wceq
    wph
    @0
    @24
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
    @24
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
    #
    cB
    cr
    wcel
    #
    @27
    cr
    wss
    ftc1.a
    ftc1.b
    cA
    cB
    iccssre
    syl2anc
    #
    ftc1.x1
    sseldd
    #
    wph
    @27
    cr
    cY
    @30
    ftc1.y1
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
    cD
    cF
    cG
    cX
    cY
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    wph
    vx
    vt
    cA
    cB
    cC
    cD
    cF
    cG
    cJ
    cK
    cL
    ftc1.g
    ftc1.a
    ftc1.b
    ftc1.le
    ftc1.s
    ftc1.d
    ftc1.i
    ftc1.c
    ftc1.f
    ftc1.j
    ftc1.k
    ftc1.l
    ftc1lem3
    #
    ftc1.x1
    ftc1.y1
    ftc1lem1
    syldan
    wph
    @21
    @23
    wceq
    @0
    wph
    vt
    @8
    @11
    @5
    caddc
    co
    #
    citg
    @21
    @23
    wph
    vt
    @8
    @35
    @10
    wph
    @9
    @8
    wcel
    #
    wa
    #
    @10
    @5
    wph
    @36
    @9
    cD
    wcel
    #
    @10
    cc
    wcel
    wph
    @8
    cD
    @9
    wph
    @8
    cA
    cB
    cioo
    co
    #
    cD
    wph
    @8
    cA
    cY
    cioo
    co
    #
    @39
    wph
    cA
    cxr
    wcel
    cA
    cX
    cle
    wbr
    #
    @8
    @40
    wss
    wph
    cA
    ftc1.a
    rexrd
    wph
    @25
    @41
    cX
    cB
    cle
    wbr
    #
    wph
    cX
    @27
    wcel
    #
    @25
    @41
    @42
    w3a
    #
    ftc1.x1
    wph
    @28
    @29
    @43
    @44
    wb
    ftc1.a
    ftc1.b
    cA
    cB
    cX
    elicc2
    syl2anc
    mpbid
    simp2d
    cA
    cX
    cY
    iooss1
    syl2anc
    wph
    cB
    cxr
    wcel
    cY
    cB
    cle
    wbr
    #
    @40
    @39
    wss
    wph
    cB
    ftc1.b
    rexrd
    wph
    @26
    cA
    cY
    cle
    wbr
    #
    @45
    wph
    cY
    @27
    wcel
    #
    @26
    @46
    @45
    w3a
    #
    ftc1.y1
    wph
    @28
    @29
    @47
    @48
    wb
    ftc1.a
    ftc1.b
    cA
    cB
    cY
    elicc2
    syl2anc
    mpbid
    simp3d
    cA
    cY
    cB
    iooss2
    syl2anc
    sstrd
    ftc1.s
    sstrd
    #
    sselda
    #
    wph
    cD
    cc
    @9
    cF
    @34
    ffvelrnda
    syldan
    #
    wph
    @5
    cc
    wcel
    #
    @36
    wph
    cD
    cc
    cC
    cF
    @34
    wph
    @39
    cD
    cC
    ftc1.s
    ftc1.c
    sseldd
    #
    ffvelrnd
    #
    adantr
    #
    npcand
    itgeq2dv
    wph
    vt
    @8
    @11
    @5
    cc
    @37
    @10
    @5
    @51
    @55
    subcld
    #
    wph
    vt
    @8
    @10
    @5
    cc
    @51
    wph
    vt
    @8
    cD
    @10
    cvv
    @49
    @8
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
    @38
    wa
    @9
    cF
    fvexd
    wph
    cF
    vt
    cD
    @10
    cmpt
    cibl
    wph
    vt
    cD
    cc
    cF
    @34
    feqmptd
    ftc1.i
    eqeltrrd
    iblss
    @55
    wph
    vt
    @8
    @5
    cmpt
    @8
    @5
    csn
    cxp
    #
    cibl
    vt
    @8
    @5
    fconstmpt
    wph
    @58
    @8
    cvol
    cfv
    #
    cr
    wcel
    #
    @52
    @61
    cibl
    wcel
    @60
    wph
    @62
    @8
    covol
    cfv
    #
    cr
    @58
    @62
    @64
    wceq
    @59
    @8
    mblvol
    ax-mp
    #
    wph
    @8
    cX
    cY
    cicc
    co
    #
    wss
    #
    @66
    cr
    wss
    #
    @66
    covol
    cfv
    #
    cr
    wcel
    @64
    cr
    wcel
    @67
    wph
    cX
    cY
    ioossicc
    a1i
    wph
    @66
    @57
    wcel
    #
    @68
    wph
    @25
    @26
    @70
    @31
    @32
    cX
    cY
    iccmbl
    syl2anc
    #
    @66
    mblss
    syl
    wph
    @66
    cvol
    cfv
    #
    @69
    cr
    wph
    @70
    @72
    @69
    wceq
    @71
    @66
    mblvol
    syl
    wph
    @25
    @26
    @72
    cr
    wcel
    @31
    @32
    cX
    cY
    iccvolcl
    syl2anc
    eqeltrrd
    @8
    @66
    ovolsscl
    syl3anc
    syl5eqel
    #
    @54
    @8
    @5
    iblconst
    syl3anc
    syl5eqelr
    #
    iblsub
    #
    @55
    @74
    itgadd
    eqtr3d
    adantr
    @1
    @22
    @18
    @12
    caddc
    @1
    @22
    @5
    @62
    cmul
    co
    #
    @18
    wph
    @22
    @76
    wceq
    #
    @0
    wph
    @58
    @63
    @52
    @77
    @60
    @73
    @54
    vt
    @8
    @5
    itgconst
    syl3anc
    adantr
    @1
    @62
    @3
    @5
    cmul
    @1
    @62
    @64
    @3
    @65
    @1
    @25
    @26
    @24
    @64
    @3
    wceq
    wph
    @25
    @0
    @31
    adantr
    wph
    @26
    @0
    @32
    adantr
    @33
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
    @12
    @18
    @3
    wph
    @12
    cc
    wcel
    @0
    wph
    vt
    @8
    @11
    cvv
    @37
    @10
    @5
    cmin
    ovexd
    #
    @75
    itgcl
    #
    adantr
    #
    @1
    @5
    @3
    wph
    @52
    @0
    @54
    adantr
    #
    @1
    @3
    wph
    @3
    cr
    wcel
    #
    @0
    wph
    cY
    cX
    @32
    @31
    resubcld
    #
    adantr
    #
    recnd
    #
    mulcld
    @86
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
    @31
    @32
    posdifd
    biimpa
    #
    gt0ne0d
    #
    divdird
    @1
    @20
    @5
    @15
    caddc
    @1
    @5
    @3
    @82
    @86
    @89
    divcan4d
    oveq2d
    3eqtrd
    oveq1d
    @1
    @15
    @5
    @1
    @12
    @3
    @81
    @86
    @89
    divcld
    @82
    pncand
    eqtrd
    fveq2d
    @1
    @12
    @3
    @81
    @86
    @89
    absdivd
    @1
    @16
    @3
    @13
    cdiv
    @1
    @3
    @85
    @1
    @87
    cc0
    @3
    cle
    wbr
    #
    @88
    @1
    cc0
    cr
    wcel
    @83
    @87
    @90
    wi
    0re
    @85
    cc0
    @3
    ltle
    sylancr
    mpd
    absidd
    oveq2d
    3eqtrd
    @1
    @14
    cE
    clt
    wbr
    #
    @13
    @3
    cE
    cmul
    co
    #
    clt
    wbr
    #
    @1
    @13
    vt
    @8
    @11
    cabs
    cfv
    #
    citg
    #
    @92
    wph
    @13
    cr
    wcel
    #
    @0
    wph
    @12
    @80
    abscld
    adantr
    wph
    @95
    cr
    wcel
    @0
    wph
    vt
    @8
    @94
    @37
    @11
    @56
    abscld
    #
    wph
    vt
    @8
    @11
    cvv
    @79
    @75
    iblabs
    #
    itgrecl
    #
    adantr
    wph
    @92
    cr
    wcel
    @0
    wph
    @3
    cE
    @84
    wph
    cE
    ftc1.e
    rpred
    #
    remulcld
    #
    adantr
    wph
    @13
    @95
    cle
    wbr
    @0
    wph
    vt
    @8
    @11
    cc
    @56
    @75
    itgabs
    adantr
    wph
    @0
    cc0
    @92
    @95
    cmin
    co
    #
    clt
    wbr
    #
    @95
    @92
    clt
    wbr
    #
    @1
    cc0
    vt
    @8
    cE
    @94
    cmin
    co
    #
    citg
    #
    @102
    clt
    @1
    vt
    @8
    @105
    @1
    cc0
    @3
    @62
    clt
    @88
    @78
    breqtrrd
    wph
    vt
    @8
    @105
    cmpt
    cibl
    wcel
    @0
    wph
    vt
    @8
    cE
    @94
    cr
    wph
    cE
    cr
    wcel
    #
    @36
    @100
    adantr
    #
    wph
    vt
    @8
    cE
    cmpt
    @8
    cE
    csn
    cxp
    #
    cibl
    vt
    @8
    cE
    fconstmpt
    wph
    @58
    @63
    cE
    cc
    wcel
    #
    @109
    cibl
    wcel
    @60
    @73
    wph
    cE
    @100
    recnd
    #
    @8
    cE
    iblconst
    syl3anc
    syl5eqelr
    #
    @97
    @98
    iblsub
    adantr
    wph
    @36
    @105
    crp
    wcel
    #
    @0
    @37
    @94
    cE
    clt
    wbr
    #
    @113
    @37
    @38
    vy
    cv
    #
    cC
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
    @115
    cF
    cfv
    #
    @5
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
    cD
    wral
    #
    @9
    cC
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
    @114
    @50
    wph
    @124
    @36
    wph
    @123
    vy
    cD
    ftc1.fc
    ralrimiva
    adantr
    @37
    @127
    cC
    cR
    cmin
    co
    #
    @9
    clt
    wbr
    @9
    cC
    cR
    caddc
    co
    #
    clt
    wbr
    @37
    @128
    cX
    @9
    wph
    @128
    cr
    wcel
    @36
    wph
    cC
    cR
    wph
    cD
    cr
    cC
    ftc1.d
    @53
    sseldd
    #
    wph
    cR
    ftc1.r
    rpred
    #
    resubcld
    adantr
    wph
    @25
    @36
    @31
    adantr
    wph
    @8
    cr
    @9
    wph
    @8
    cD
    cr
    @49
    ftc1.d
    sstrd
    sselda
    #
    wph
    @128
    cX
    clt
    wbr
    #
    @36
    wph
    @133
    cX
    @129
    clt
    wbr
    #
    wph
    cX
    cC
    cmin
    co
    cabs
    cfv
    cR
    clt
    wbr
    @133
    @134
    wa
    ftc1.x2
    wph
    cX
    cC
    cR
    @31
    @130
    @131
    absdifltd
    mpbid
    simpld
    adantr
    @37
    cX
    @9
    clt
    wbr
    #
    @9
    cY
    clt
    wbr
    #
    @36
    @135
    @136
    wa
    wph
    @9
    cX
    cY
    eliooord
    adantl
    #
    simpld
    lttrd
    @37
    @9
    cY
    @129
    @132
    wph
    @26
    @36
    @32
    adantr
    wph
    @129
    cr
    wcel
    @36
    wph
    cC
    cR
    @130
    @131
    readdcld
    adantr
    @37
    @135
    @136
    @137
    simprd
    wph
    cY
    @129
    clt
    wbr
    #
    @36
    wph
    @128
    cY
    clt
    wbr
    #
    @138
    wph
    cY
    cC
    cmin
    co
    cabs
    cfv
    cR
    clt
    wbr
    @139
    @138
    wa
    ftc1.y2
    wph
    cY
    cC
    cR
    @32
    @130
    @131
    absdifltd
    mpbid
    simprd
    adantr
    lttrd
    @37
    @9
    cC
    cR
    @132
    wph
    cC
    cr
    wcel
    @36
    @130
    adantr
    wph
    cR
    cr
    wcel
    @36
    @131
    adantr
    absdifltd
    mpbir2and
    @123
    @127
    @114
    wi
    vy
    @9
    cD
    @115
    @9
    wceq
    #
    @118
    @127
    @122
    @114
    @140
    @117
    @126
    cR
    clt
    @140
    @116
    @125
    cabs
    @115
    @9
    cC
    cmin
    oveq1
    fveq2d
    breq1d
    @140
    @121
    @94
    cE
    clt
    @140
    @120
    @11
    cabs
    @140
    @119
    @10
    @5
    cmin
    @115
    @9
    cF
    fveq2
    oveq1d
    fveq2d
    breq1d
    imbi12d
    rspcv
    syl3c
    @37
    @94
    cr
    wcel
    @107
    @114
    @113
    wb
    @97
    @108
    @94
    cE
    difrp
    syl2anc
    mpbid
    adantlr
    itggt0
    @1
    @106
    vt
    @8
    cE
    citg
    #
    @95
    cmin
    co
    #
    @102
    wph
    @106
    @142
    wceq
    @0
    wph
    vt
    @8
    cE
    @94
    cr
    @108
    @112
    @97
    @98
    itgsub
    adantr
    @1
    @141
    @92
    @95
    cmin
    @1
    @141
    cE
    @62
    cmul
    co
    #
    cE
    @3
    cmul
    co
    #
    @92
    wph
    @141
    @143
    wceq
    #
    @0
    wph
    @58
    @63
    @110
    @145
    @60
    @73
    @111
    vt
    @8
    cE
    itgconst
    syl3anc
    adantr
    @1
    @62
    @3
    cE
    cmul
    @78
    oveq2d
    wph
    @144
    @92
    wceq
    @0
    wph
    cE
    @3
    @111
    wph
    @3
    @84
    recnd
    mulcomd
    adantr
    3eqtrd
    oveq1d
    eqtrd
    breqtrd
    wph
    @104
    @103
    wph
    @95
    @92
    @99
    @101
    posdifd
    biimpar
    syldan
    lelttrd
    @1
    @96
    @107
    @83
    @87
    @91
    @93
    wb
    @1
    @12
    @81
    abscld
    wph
    @107
    @0
    @100
    adantr
    @85
    @88
    @13
    cE
    @3
    ltdivmul
    syl112anc
    mpbird
    eqbrtrd
end
