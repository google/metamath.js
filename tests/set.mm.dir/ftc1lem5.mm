include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cicc.mm"
include "cr.mm"
include "wcel.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "cioo.mm"
include "ioossicc.mm"
include "sseldi.mm"
include "lttri2d.mm"
include "biimpa.mm"
include "wa.mm"
include "cdiv.mm"
include "cneg.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "adantr.mm"
include "simpr.mm"
include "ltned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cv.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cc.mm"
include "ftc1lem3.mm"
include "ftc1lem2.mm"
include "ffvelrnd.mm"
include "subcld.mm"
include "recnd.mm"
include "cc0.mm"
include "subeq0ad.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "syldan.mm"
include "div2negd.mm"
include "negsubdi2d.mm"
include "3eqtr2d.mm"
include "fveq2d.mm"
include "subidd.mm"
include "abs00bd.mm"
include "rpgt0d.mm"
include "eqbrtrd.mm"
include "ftc1lem4.mm"
include "gtned.mm"
include "jaodan.mm"

theorem ftc1lem5
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
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  let cY: class Y
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
  disjoint Y t
  disjoint Y x
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
  assert |- ( ( ph /\ X =/= C ) -> ( abs ` ( ( H ` X ) - ( F ` C ) ) ) < E )

  proof
    wph
    cX
    cC
    wne
    #
    cX
    cC
    clt
    wbr
    #
    cC
    cX
    clt
    wbr
    #
    wo
    #
    cX
    cH
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
    cE
    clt
    wbr
    #
    wph
    @0
    @3
    wph
    cX
    cC
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
    @9
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
    @9
    cr
    cC
    @10
    wph
    cA
    cB
    cioo
    co
    @9
    cC
    cA
    cB
    ioossicc
    ftc1.c
    sseldi
    #
    sseldd
    #
    lttri2d
    biimpa
    wph
    @1
    @8
    @2
    wph
    @1
    wa
    #
    @7
    cC
    cG
    cfv
    #
    cX
    cG
    cfv
    #
    cmin
    co
    #
    cC
    cX
    cmin
    co
    #
    cdiv
    co
    #
    @5
    cmin
    co
    #
    cabs
    cfv
    cE
    clt
    @14
    @6
    @20
    cabs
    @14
    @4
    @19
    @5
    cmin
    @14
    @4
    @16
    @15
    cmin
    co
    #
    cX
    cC
    cmin
    co
    #
    cdiv
    co
    #
    @21
    cneg
    #
    @22
    cneg
    #
    cdiv
    co
    #
    @19
    @14
    cX
    @9
    cC
    csn
    cdif
    #
    wcel
    #
    @4
    @23
    wceq
    #
    @14
    cX
    @9
    wcel
    #
    @0
    @28
    wph
    @30
    @1
    ftc1.x1
    adantr
    @14
    cX
    cC
    wph
    cX
    cr
    wcel
    @1
    @11
    adantr
    wph
    @1
    simpr
    ltned
    #
    cX
    @9
    cC
    eldifsn
    #
    sylanbrc
    vz
    cX
    vz
    cv
    #
    cG
    cfv
    #
    @15
    cmin
    co
    #
    @33
    cC
    cmin
    co
    #
    cdiv
    co
    @23
    @27
    cH
    @33
    cX
    wceq
    #
    @35
    @21
    @36
    @22
    cdiv
    @37
    @34
    @16
    @15
    cmin
    @33
    cX
    cG
    fveq2
    oveq1d
    @33
    cX
    cC
    cmin
    oveq1
    oveq12d
    ftc1.h
    @21
    @22
    cdiv
    ovex
    fvmpt
    #
    syl
    @14
    @21
    @22
    wph
    @21
    cc
    wcel
    @1
    wph
    @16
    @15
    wph
    @9
    cc
    cX
    cG
    wph
    vx
    vt
    cA
    cB
    cD
    cF
    cG
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
    ftc1lem2
    #
    ftc1.x1
    ffvelrnd
    #
    wph
    @9
    cc
    cC
    cG
    @39
    @12
    ffvelrnd
    #
    subcld
    adantr
    wph
    @22
    cc
    wcel
    @1
    wph
    cX
    cC
    wph
    cX
    @11
    recnd
    #
    wph
    cC
    @13
    recnd
    #
    subcld
    adantr
    wph
    @1
    @0
    @22
    cc0
    wne
    #
    @31
    wph
    @44
    @0
    wph
    @22
    cc0
    cX
    cC
    wph
    cX
    cC
    @42
    @43
    subeq0ad
    necon3bid
    biimpar
    syldan
    div2negd
    wph
    @26
    @19
    wceq
    @1
    wph
    @24
    @17
    @25
    @18
    cdiv
    wph
    @16
    @15
    @40
    @41
    negsubdi2d
    wph
    cX
    cC
    @42
    @43
    negsubdi2d
    oveq12d
    adantr
    3eqtr2d
    oveq1d
    fveq2d
    wph
    vx
    vy
    vz
    vt
    cA
    cB
    cC
    cD
    cR
    cE
    cF
    cG
    cH
    cJ
    cK
    cL
    cX
    cC
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
    ftc1.h
    ftc1.e
    ftc1.r
    ftc1.fc
    ftc1.x1
    ftc1.x2
    @12
    wph
    cC
    cC
    cmin
    co
    #
    cabs
    cfv
    cc0
    cR
    clt
    wph
    @45
    wph
    cC
    @43
    subidd
    abs00bd
    wph
    cR
    ftc1.r
    rpgt0d
    eqbrtrd
    #
    ftc1lem4
    eqbrtrd
    wph
    @2
    wa
    #
    @7
    @23
    @5
    cmin
    co
    #
    cabs
    cfv
    cE
    clt
    @47
    @6
    @48
    cabs
    @47
    @4
    @23
    @5
    cmin
    @47
    @28
    @29
    @47
    @30
    @0
    @28
    wph
    @30
    @2
    ftc1.x1
    adantr
    @47
    cC
    cX
    wph
    cC
    cr
    wcel
    @2
    @13
    adantr
    wph
    @2
    simpr
    gtned
    @32
    sylanbrc
    @38
    syl
    oveq1d
    fveq2d
    wph
    vx
    vy
    vz
    vt
    cA
    cB
    cC
    cD
    cR
    cE
    cF
    cG
    cH
    cJ
    cK
    cL
    cC
    cX
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
    ftc1.h
    ftc1.e
    ftc1.r
    ftc1.fc
    @12
    @46
    ftc1.x1
    ftc1.x2
    ftc1lem4
    eqbrtrd
    jaodan
    syldan
end
