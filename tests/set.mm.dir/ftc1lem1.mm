include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cioo.mm"
include "cv.mm"
include "citg.mm"
include "caddc.mm"
include "wceq.mm"
include "cicc.mm"
include "wcel.mm"
include "oveq2.mm"
include "itgeq1.mm"
include "syl.mm"
include "itgex.mm"
include "fvmpt.mm"
include "adantr.mm"
include "cr.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "mpbid.mm"
include "simp2d.mm"
include "simpr.mm"
include "mpbir3and.mm"
include "cc.mm"
include "cxr.mm"
include "rexrd.mm"
include "simp3d.mm"
include "iooss2.mm"
include "sstrd.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "syldan.mm"
include "cmpt.mm"
include "cibl.mm"
include "cvv.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "a1i.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "iblss.mm"
include "iooss1.mm"
include "itgsplitioo.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "itgcl.mm"
include "pncan2d.mm"

theorem ftc1lem1
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vd: setvar d
  let vr: setvar r
  let ve: setvar e
  let cE: class E
  let cH: class H
  let cL: class L
  let cR: class R
  assume ftc1.g: |- G = ( x e. ( A [,] B ) |-> S. ( A (,) x ) ( F ` t ) _d t )
  assume ftc1.a: |- ( ph -> A e. RR )
  assume ftc1.b: |- ( ph -> B e. RR )
  assume ftc1.le: |- ( ph -> A <_ B )
  assume ftc1.s: |- ( ph -> ( A (,) B ) C_ D )
  assume ftc1.d: |- ( ph -> D C_ RR )
  assume ftc1.i: |- ( ph -> F e. L^1 )
  assume ftc1a.f: |- ( ph -> F : D --> CC )
  assume ftc1lem1.x: |- ( ph -> X e. ( A [,] B ) )
  assume ftc1lem1.y: |- ( ph -> Y e. ( A [,] B ) )

  disjoint t x
  disjoint D t
  disjoint D x
  disjoint A t
  disjoint A x
  disjoint B t
  disjoint B x
  disjoint X t
  disjoint X x
  disjoint ph t
  disjoint ph x
  disjoint Y t
  disjoint Y x
  disjoint F t
  disjoint F x
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
  disjoint t y
  disjoint t z
  disjoint C t
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
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
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
  disjoint D y
  disjoint D z
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
  disjoint G y
  disjoint G z
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
  disjoint A y
  disjoint A z
  disjoint B d
  disjoint B e
  disjoint B r
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint X z
  disjoint E t
  disjoint E y
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint d ph
  disjoint e ph
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint F d
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint L s
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint R y
  assert |- ( ( ph /\ X <_ Y ) -> ( ( G ` Y ) - ( G ` X ) ) = S. ( X (,) Y ) ( F ` t ) _d t )

  proof
    wph
    cX
    cY
    cle
    wbr
    #
    wa
    #
    cY
    cG
    cfv
    #
    cX
    cG
    cfv
    #
    cmin
    co
    vt
    cA
    cX
    cioo
    co
    #
    vt
    cv
    #
    cF
    cfv
    #
    citg
    #
    vt
    cX
    cY
    cioo
    co
    #
    @6
    citg
    #
    caddc
    co
    #
    @7
    cmin
    co
    #
    @9
    @1
    @2
    @10
    @3
    @7
    cmin
    @1
    @2
    vt
    cA
    cY
    cioo
    co
    #
    @6
    citg
    #
    @10
    wph
    @2
    @13
    wceq
    #
    @0
    wph
    cY
    cA
    cB
    cicc
    co
    #
    wcel
    #
    @14
    ftc1lem1.y
    vx
    cY
    vt
    cA
    vx
    cv
    #
    cioo
    co
    #
    @6
    citg
    #
    @13
    @15
    cG
    @17
    cY
    wceq
    @18
    @12
    wceq
    @19
    @13
    wceq
    @17
    cY
    cA
    cioo
    oveq2
    vt
    @18
    @12
    @6
    itgeq1
    syl
    ftc1.g
    vt
    @12
    @6
    itgex
    fvmpt
    syl
    adantr
    @1
    vt
    cA
    cX
    cY
    @6
    wph
    cA
    cr
    wcel
    #
    @0
    ftc1.a
    adantr
    wph
    cY
    cr
    wcel
    #
    @0
    wph
    @15
    cr
    cY
    wph
    @20
    cB
    cr
    wcel
    #
    @15
    cr
    wss
    ftc1.a
    ftc1.b
    cA
    cB
    iccssre
    syl2anc
    #
    ftc1lem1.y
    sseldd
    #
    adantr
    @1
    cX
    cA
    cY
    cicc
    co
    wcel
    #
    cX
    cr
    wcel
    #
    cA
    cX
    cle
    wbr
    #
    @0
    wph
    @26
    @0
    wph
    @15
    cr
    cX
    @23
    ftc1lem1.x
    sseldd
    adantr
    wph
    @27
    @0
    wph
    @26
    @27
    cX
    cB
    cle
    wbr
    #
    wph
    cX
    @15
    wcel
    #
    @26
    @27
    @28
    w3a
    #
    ftc1lem1.x
    wph
    @20
    @22
    @29
    @30
    wb
    ftc1.a
    ftc1.b
    cA
    cB
    cX
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    #
    adantr
    wph
    @0
    simpr
    wph
    @25
    @26
    @27
    @0
    w3a
    wb
    #
    @0
    wph
    @20
    @21
    @33
    ftc1.a
    @24
    cA
    cY
    cX
    elicc2
    syl2anc
    adantr
    mpbir3and
    @1
    @5
    @12
    wcel
    @5
    cD
    wcel
    #
    @6
    cc
    wcel
    #
    @1
    @12
    cD
    @5
    wph
    @12
    cD
    wss
    @0
    wph
    @12
    cA
    cB
    cioo
    co
    #
    cD
    wph
    cB
    cxr
    wcel
    #
    cY
    cB
    cle
    wbr
    #
    @12
    @36
    wss
    wph
    cB
    ftc1.b
    rexrd
    #
    wph
    @21
    cA
    cY
    cle
    wbr
    #
    @38
    wph
    @16
    @21
    @40
    @38
    w3a
    #
    ftc1lem1.y
    wph
    @20
    @22
    @16
    @41
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
    #
    ftc1.s
    sstrd
    adantr
    sselda
    wph
    @34
    @35
    @0
    wph
    cD
    cc
    @5
    cF
    ftc1a.f
    ffvelrnda
    #
    adantlr
    syldan
    wph
    vt
    @4
    @6
    cmpt
    cibl
    wcel
    @0
    wph
    vt
    @4
    cD
    @6
    cvv
    wph
    @4
    @36
    cD
    wph
    @37
    @28
    @4
    @36
    wss
    @39
    wph
    @26
    @27
    @28
    @31
    simp3d
    cA
    cX
    cB
    iooss2
    syl2anc
    ftc1.s
    sstrd
    @4
    cvol
    cdm
    #
    wcel
    wph
    cA
    cX
    ioombl
    a1i
    wph
    @34
    wa
    @5
    cF
    fvexd
    #
    wph
    cF
    vt
    cD
    @6
    cmpt
    cibl
    wph
    vt
    cD
    cc
    cF
    ftc1a.f
    feqmptd
    ftc1.i
    eqeltrrd
    #
    iblss
    #
    adantr
    wph
    vt
    @8
    @6
    cmpt
    cibl
    wcel
    @0
    wph
    vt
    @8
    cD
    @6
    cvv
    wph
    @8
    @36
    cD
    wph
    @8
    @12
    @36
    wph
    cA
    cxr
    wcel
    @27
    @8
    @12
    wss
    wph
    cA
    ftc1.a
    rexrd
    @32
    cA
    cX
    cY
    iooss1
    syl2anc
    @42
    sstrd
    ftc1.s
    sstrd
    #
    @8
    @44
    wcel
    wph
    cX
    cY
    ioombl
    a1i
    @45
    @46
    iblss
    #
    adantr
    itgsplitioo
    eqtrd
    wph
    @3
    @7
    wceq
    #
    @0
    wph
    @29
    @50
    ftc1lem1.x
    vx
    cX
    @19
    @7
    @15
    cG
    @17
    cX
    wceq
    @18
    @4
    wceq
    @19
    @7
    wceq
    @17
    cX
    cA
    cioo
    oveq2
    vt
    @18
    @4
    @6
    itgeq1
    syl
    ftc1.g
    vt
    @4
    @6
    itgex
    fvmpt
    syl
    adantr
    oveq12d
    wph
    @11
    @9
    wceq
    @0
    wph
    @7
    @9
    wph
    vt
    @4
    @6
    cvv
    wph
    @5
    @4
    wcel
    wa
    @5
    cF
    fvexd
    @47
    itgcl
    wph
    vt
    @8
    @6
    cc
    wph
    @5
    @8
    wcel
    @34
    @35
    wph
    @8
    cD
    @5
    @48
    sselda
    @43
    syldan
    @49
    itgcl
    pncan2d
    adantr
    eqtrd
end
