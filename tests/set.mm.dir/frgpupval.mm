include "cv.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ovexd.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "cid.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wceq.mm"
include "coeq2.mm"
include "oveq2d.mm"
include "wf.mm"
include "wfun.mm"
include "frgpupf.mm"
include "ffun.mm"
include "syl.mm"
include "qliftval.mm"

theorem frgpupval
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let c.sm: class .~
  let cT: class T
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
  assert |- ( ( ph /\ A e. W ) -> ( E ` [ A ] .~ ) = ( H gsum ( T o. A ) ) )

  proof
    wph
    vg
    cH
    cT
    vg
    cv
    #
    ccom
    #
    cgsu
    co
    cH
    cT
    cA
    ccom
    #
    cgsu
    co
    cA
    c.sm
    cE
    cW
    cvv
    frgpup.e
    wph
    @0
    cW
    wcel
    wa
    cH
    @1
    cgsu
    ovexd
    cW
    c.sm
    wer
    wph
    c.sm
    cI
    cW
    frgpup.w
    frgpup.r
    efger
    a1i
    cW
    cvv
    wcel
    wph
    cW
    cI
    c2o
    cxp
    cword
    #
    cid
    cfv
    cvv
    frgpup.w
    @3
    cid
    fvex
    eqeltri
    a1i
    @0
    cA
    wceq
    @1
    @2
    cH
    cgsu
    @0
    cA
    cT
    coeq2
    oveq2d
    wph
    cX
    cB
    cE
    wf
    cE
    wfun
    wph
    vy
    vz
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
    frgpupf
    cX
    cB
    cE
    ffun
    syl
    qliftval
end
