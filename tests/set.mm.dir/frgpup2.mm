include "cfv.mm"
include "c0.mm"
include "cop.mm"
include "cs1.mm"
include "cec.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "vrgpval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "c1o.mm"
include "cpr.mm"
include "0ex.mm"
include "prid1.mm"
include "df2o3.mm"
include "eleqtrri.mm"
include "opelxpi.mm"
include "sylancl.mm"
include "s1cld.mm"
include "cid.mm"
include "cvv.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "wrdexg.mm"
include "fvi.mm"
include "3syl.mm"
include "syl5eq.mm"
include "eleqtrrd.mm"
include "frgpupval.mm"
include "mpdan.mm"
include "wf.mm"
include "frgpuptf.mm"
include "s1co.mm"
include "df-ov.mm"
include "cv.mm"
include "cif.mm"
include "iftrue.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "syl5eqr.mm"
include "s1eqd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ffvelrnd.mm"
include "gsumws1.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem frgpup2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let c.sm: class .~
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vc: setvar c
  let vh: setvar h
  let vt: setvar t
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let cK: class K
  let cM: class M
  assume frgpup.b: |- B = ( Base ` H )
  assume frgpup.n: |- N = ( invg ` H )
  assume frgpup.t: |- T = ( y e. I , z e. 2o |-> if ( z = (/) , ( F ` y ) , ( N ` ( F ` y ) ) ) )
  assume frgpup.h: |- ( ph -> H e. Grp )
  assume frgpup.i: |- ( ph -> I e. V )
  assume frgpup.a: |- ( ph -> F : I --> B )
  assume frgpup.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpup.r: |- .~ = ( ~FG ` I )
  assume frgpup.g: |- G = ( freeGrp ` I )
  assume frgpup.x: |- X = ( Base ` G )
  assume frgpup.e: |- E = ran ( g e. W |-> <. [ g ] .~ , ( H gsum ( T o. g ) ) >. )
  assume frgpup.u: |- U = ( varFGrp ` I )
  assume frgpup.y: |- ( ph -> A e. I )

  disjoint g y
  disjoint g z
  disjoint A g
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint H g
  disjoint F y
  disjoint F z
  disjoint N y
  disjoint N z
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint T g
  disjoint .~ g
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint I y
  disjoint I z
  disjoint W g
  disjoint a b
  disjoint a g
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint g u
  disjoint g v
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint a c
  disjoint a h
  disjoint a t
  disjoint E a
  disjoint c h
  disjoint c t
  disjoint c u
  disjoint E c
  disjoint h t
  disjoint h u
  disjoint E h
  disjoint t u
  disjoint E t
  disjoint E u
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint H a
  disjoint b c
  disjoint b h
  disjoint b n
  disjoint b r
  disjoint b t
  disjoint b x
  disjoint H b
  disjoint c g
  disjoint c n
  disjoint c r
  disjoint c v
  disjoint c x
  disjoint H c
  disjoint g h
  disjoint g n
  disjoint g r
  disjoint g t
  disjoint g x
  disjoint h n
  disjoint h r
  disjoint h v
  disjoint h x
  disjoint H h
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint H n
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint H r
  disjoint t v
  disjoint t x
  disjoint H t
  disjoint u x
  disjoint H u
  disjoint v x
  disjoint H v
  disjoint H x
  disjoint C u
  disjoint C v
  disjoint a i
  disjoint a j
  disjoint a w
  disjoint K a
  disjoint i j
  disjoint i n
  disjoint i t
  disjoint i w
  disjoint K i
  disjoint j n
  disjoint j t
  disjoint j w
  disjoint K j
  disjoint n w
  disjoint K n
  disjoint t w
  disjoint K t
  disjoint K w
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint B a
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint G a
  disjoint c w
  disjoint G c
  disjoint G t
  disjoint u w
  disjoint G u
  disjoint G w
  disjoint T a
  disjoint b i
  disjoint b j
  disjoint T b
  disjoint g i
  disjoint g j
  disjoint h i
  disjoint h j
  disjoint T h
  disjoint i r
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint T i
  disjoint j r
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint T j
  disjoint T n
  disjoint T r
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint .~ a
  disjoint b w
  disjoint .~ b
  disjoint g w
  disjoint h w
  disjoint .~ h
  disjoint .~ i
  disjoint .~ j
  disjoint .~ n
  disjoint r w
  disjoint .~ r
  disjoint .~ t
  disjoint .~ u
  disjoint w x
  disjoint .~ w
  disjoint .~ x
  disjoint a ph
  disjoint b ph
  disjoint c i
  disjoint c j
  disjoint c ph
  disjoint h ph
  disjoint i y
  disjoint i z
  disjoint i ph
  disjoint j y
  disjoint j z
  disjoint j ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint I a
  disjoint I b
  disjoint I i
  disjoint I j
  disjoint I n
  disjoint r y
  disjoint r z
  disjoint I r
  disjoint I w
  disjoint I x
  disjoint V w
  disjoint W a
  disjoint W b
  disjoint W h
  disjoint W n
  disjoint W r
  disjoint W t
  disjoint W u
  disjoint v w
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X n
  disjoint X u
  disjoint X w
  assert |- ( ph -> ( E ` ( U ` A ) ) = ( F ` A ) )

  proof
    wph
    cA
    cU
    cfv
    #
    cE
    cfv
    cA
    c0
    cop
    #
    cs1
    #
    c.sm
    cec
    #
    cE
    cfv
    #
    cH
    cT
    @2
    ccom
    #
    cgsu
    co
    #
    cA
    cF
    cfv
    #
    wph
    @0
    @3
    cE
    wph
    cI
    cV
    wcel
    #
    cA
    cI
    wcel
    #
    @0
    @3
    wceq
    frgpup.i
    frgpup.y
    cA
    c.sm
    cU
    cI
    cV
    frgpup.r
    frgpup.u
    vrgpval
    syl2anc
    fveq2d
    wph
    @2
    cW
    wcel
    @4
    @6
    wceq
    wph
    @2
    cI
    c2o
    cxp
    #
    cword
    #
    cW
    wph
    @1
    @10
    wph
    @9
    c0
    c2o
    wcel
    #
    @1
    @10
    wcel
    #
    frgpup.y
    c0
    c0
    c1o
    cpr
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    #
    cA
    c0
    cI
    c2o
    opelxpi
    sylancl
    #
    s1cld
    wph
    cW
    @11
    cid
    cfv
    #
    @11
    frgpup.w
    wph
    @10
    cvv
    wcel
    #
    @11
    cvv
    wcel
    @16
    @11
    wceq
    wph
    @8
    c2o
    con0
    wcel
    @17
    frgpup.i
    2on
    cI
    c2o
    cV
    con0
    xpexg
    sylancl
    @10
    cvv
    wrdexg
    @11
    cvv
    fvi
    3syl
    syl5eq
    eleqtrrd
    wph
    vy
    vz
    @2
    cB
    c.sm
    cT
    vg
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    cW
    cX
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpup.g
    frgpup.x
    frgpup.e
    frgpupval
    mpdan
    wph
    @6
    cH
    @7
    cs1
    #
    cgsu
    co
    #
    @7
    wph
    @5
    @18
    cH
    cgsu
    wph
    @5
    @1
    cT
    cfv
    #
    cs1
    #
    @18
    wph
    @13
    @10
    cB
    cT
    wf
    @5
    @21
    wceq
    @15
    wph
    vy
    vz
    cB
    cT
    cF
    cH
    cI
    cN
    cV
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpuptf
    @10
    cB
    @1
    cT
    s1co
    syl2anc
    wph
    @20
    @7
    wph
    @20
    cA
    c0
    cT
    co
    #
    @7
    cA
    c0
    cT
    df-ov
    wph
    @9
    @12
    @22
    @7
    wceq
    frgpup.y
    @14
    vy
    vz
    cA
    c0
    cI
    c2o
    vz
    cv
    c0
    wceq
    #
    vy
    cv
    #
    cF
    cfv
    #
    @25
    cN
    cfv
    #
    cif
    #
    @7
    cT
    @23
    @24
    cA
    wceq
    @27
    @25
    @7
    @23
    @25
    @26
    iftrue
    @24
    cA
    cF
    fveq2
    sylan9eqr
    frgpup.t
    cA
    cF
    fvex
    ovmpt2a
    sylancl
    syl5eqr
    s1eqd
    eqtrd
    oveq2d
    wph
    @7
    cB
    wcel
    @19
    @7
    wceq
    wph
    cI
    cB
    cA
    cF
    frgpup.a
    frgpup.y
    ffvelrnd
    cB
    @7
    cH
    frgpup.b
    gsumws1
    syl
    eqtrd
    3eqtrd
end
