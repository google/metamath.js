include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "wcel.mm"
include "c2o.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "cgrp.mm"
include "adantr.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ifcld.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"

theorem frgpuptf
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let cA: class A
  let vc: setvar c
  let vh: setvar h
  let vt: setvar t
  let cE: class E
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let cK: class K
  let cM: class M
  let cG: class G
  let c.sm: class .~
  let cW: class W
  let cX: class X
  assume frgpup.b: |- B = ( Base ` H )
  assume frgpup.n: |- N = ( invg ` H )
  assume frgpup.t: |- T = ( y e. I , z e. 2o |-> if ( z = (/) , ( F ` y ) , ( N ` ( F ` y ) ) ) )
  assume frgpup.h: |- ( ph -> H e. Grp )
  assume frgpup.i: |- ( ph -> I e. V )
  assume frgpup.a: |- ( ph -> F : I --> B )

  disjoint y z
  disjoint F y
  disjoint F z
  disjoint N y
  disjoint N z
  disjoint B y
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint I y
  disjoint I z
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
  disjoint g y
  disjoint g z
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
  disjoint H g
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
  disjoint B g
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
  disjoint T g
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
  disjoint .~ g
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
  disjoint g ph
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
  disjoint W g
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
  assert |- ( ph -> T : ( I X. 2o ) --> B )

  proof
    wph
    vz
    cv
    #
    c0
    wceq
    #
    vy
    cv
    #
    cF
    cfv
    #
    @3
    cN
    cfv
    #
    cif
    #
    cB
    wcel
    #
    vz
    c2o
    wral
    vy
    cI
    wral
    cI
    c2o
    cxp
    cB
    cT
    wf
    wph
    @6
    vy
    vz
    cI
    c2o
    wph
    @2
    cI
    wcel
    #
    @0
    c2o
    wcel
    #
    wa
    #
    wa
    #
    @1
    @3
    @4
    cB
    wph
    @7
    @3
    cB
    wcel
    #
    @8
    wph
    cI
    cB
    @2
    cF
    frgpup.a
    ffvelrnda
    adantrr
    #
    @10
    cH
    cgrp
    wcel
    #
    @11
    @4
    cB
    wcel
    wph
    @13
    @9
    frgpup.h
    adantr
    @12
    cB
    cH
    cN
    @3
    frgpup.b
    frgpup.n
    grpinvcl
    syl2anc
    ifcld
    ralrimivva
    vy
    vz
    cI
    c2o
    @5
    cB
    cT
    frgpup.t
    fmpt2
    sylib
end
