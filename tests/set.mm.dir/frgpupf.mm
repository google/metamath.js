include "wf.mm"
include "cqs.mm"
include "wfun.mm"
include "cv.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmnd.mm"
include "cword.mm"
include "cgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "adantr.mm"
include "c2o.mm"
include "cxp.mm"
include "cid.mm"
include "cfv.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "frgpuptf.mm"
include "wrdco.mm"
include "syl2anr.mm"
include "gsumwcl.mm"
include "syl2anc.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "wceq.mm"
include "coeq2.mm"
include "oveq2d.mm"
include "frgpuplem.mm"
include "qliftfund.mm"
include "qliftf.mm"
include "mpbid.mm"
include "cbs.mm"
include "cfrmd.mm"
include "cqus.mm"
include "eqid.mm"
include "frgpval.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "wrdexg.mm"
include "fvi.mm"
include "3syl.mm"
include "syl5eq.mm"
include "frmdbas.mm"
include "eqtr4d.mm"
include "cefg.mm"
include "fvexd.mm"
include "qusbas.mm"
include "syl6reqr.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem frgpupf
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
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
  let cA: class A
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
  disjoint y z
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
  disjoint A g
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A y
  disjoint A z
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
  assert |- ( ph -> E : X --> B )

  proof
    wph
    cX
    cB
    cE
    wf
    cW
    c.sm
    cqs
    #
    cB
    cE
    wf
    #
    wph
    cE
    wfun
    @1
    wph
    vg
    vh
    cH
    cT
    vg
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cH
    cT
    vh
    cv
    #
    ccom
    #
    cgsu
    co
    c.sm
    cE
    cW
    cB
    frgpup.e
    wph
    @2
    cW
    wcel
    #
    wa
    cH
    cmnd
    wcel
    #
    @3
    cB
    cword
    wcel
    #
    @4
    cB
    wcel
    wph
    @8
    @7
    wph
    cH
    cgrp
    wcel
    @8
    frgpup.h
    cH
    grpmnd
    syl
    adantr
    @7
    @2
    cI
    c2o
    cxp
    #
    cword
    #
    wcel
    @10
    cB
    cT
    wf
    @9
    wph
    cW
    @11
    @2
    cW
    @11
    cid
    cfv
    #
    @11
    frgpup.w
    @11
    fviss
    eqsstri
    sseli
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
    cT
    @2
    wrdco
    syl2anr
    cB
    cH
    @3
    frgpup.b
    gsumwcl
    syl2anc
    #
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
    #
    cW
    cvv
    wcel
    wph
    cW
    @12
    cvv
    frgpup.w
    @11
    cid
    fvex
    eqeltri
    a1i
    #
    @2
    @5
    wceq
    @3
    @6
    cH
    cgsu
    @2
    @5
    cT
    coeq2
    oveq2d
    wph
    vy
    vz
    @2
    cB
    @5
    c.sm
    cT
    cF
    cH
    cI
    cN
    cV
    cW
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpuplem
    qliftfund
    wph
    vg
    @4
    c.sm
    cE
    cW
    cB
    frgpup.e
    @13
    @14
    @15
    qliftf
    mpbid
    wph
    cX
    @0
    cB
    cE
    wph
    @0
    cG
    cbs
    cfv
    cX
    wph
    c.sm
    @10
    cfrmd
    cfv
    #
    cG
    cW
    cvv
    cvv
    wph
    cI
    cV
    wcel
    #
    cG
    @16
    c.sm
    cqus
    co
    wceq
    frgpup.i
    c.sm
    cG
    cI
    @16
    cV
    frgpup.g
    @16
    eqid
    #
    frgpup.r
    frgpval
    syl
    wph
    cW
    @11
    @16
    cbs
    cfv
    #
    wph
    cW
    @12
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
    @12
    @11
    wceq
    wph
    @17
    c2o
    con0
    wcel
    @20
    frgpup.i
    2on
    cI
    c2o
    cV
    con0
    xpexg
    sylancl
    #
    @10
    cvv
    wrdexg
    @11
    cvv
    fvi
    3syl
    syl5eq
    wph
    @20
    @19
    @11
    wceq
    @21
    @19
    @10
    @16
    cvv
    @18
    @19
    eqid
    frmdbas
    syl
    eqtr4d
    c.sm
    cvv
    wcel
    wph
    c.sm
    cI
    cefg
    cfv
    cvv
    frgpup.r
    cI
    cefg
    fvex
    eqeltri
    a1i
    wph
    @10
    cfrmd
    fvexd
    qusbas
    frgpup.x
    syl6reqr
    feq2d
    mpbird
end
