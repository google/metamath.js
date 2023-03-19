include "c2o.mm"
include "cxp.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wrex.mm"
include "elxp2.mm"
include "wa.mm"
include "co.mm"
include "c1o.mm"
include "cdif.mm"
include "efgmval.mm"
include "adantl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "c0.mm"
include "wo.mm"
include "cpr.mm"
include "elpri.mm"
include "df2o3.mm"
include "eleq2s.mm"
include "simpr.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "prid2.mm"
include "eleqtrri.mm"
include "cif.mm"
include "wne.mm"
include "1n0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "ifnefalse.mm"
include "syl.mm"
include "fveq2.mm"
include "sylan9eqr.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "sylancl.mm"
include "0ex.mm"
include "prid1.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "difeq2.mm"
include "dif0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "cgrp.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "grpinvinv.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "difid.mm"
include "jaod.mm"
include "syl5.mm"
include "impr.mm"
include "eqtrd.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "imp.mm"

theorem frgpuptinv
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cI: class I
  let cM: class M
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
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
  assume frgpuptinv.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )

  disjoint y z
  disjoint A y
  disjoint A z
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
  assert |- ( ( ph /\ A e. ( I X. 2o ) ) -> ( T ` ( M ` A ) ) = ( N ` ( T ` A ) ) )

  proof
    wph
    cA
    cI
    c2o
    cxp
    wcel
    #
    cA
    cM
    cfv
    #
    cT
    cfv
    #
    cA
    cT
    cfv
    #
    cN
    cfv
    #
    wceq
    #
    @0
    cA
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    vb
    c2o
    wrex
    va
    cI
    wrex
    wph
    @5
    va
    vb
    cA
    cI
    c2o
    elxp2
    wph
    @9
    @5
    va
    vb
    cI
    c2o
    wph
    @6
    cI
    wcel
    #
    @7
    c2o
    wcel
    #
    wa
    #
    wa
    #
    @5
    @9
    @6
    @7
    cM
    co
    #
    cT
    cfv
    #
    @6
    @7
    cT
    co
    #
    cN
    cfv
    #
    wceq
    @13
    @15
    @6
    c1o
    @7
    cdif
    #
    cT
    co
    #
    @17
    @13
    @15
    @6
    @18
    cop
    #
    cT
    cfv
    @19
    @13
    @14
    @20
    cT
    @12
    @14
    @20
    wceq
    wph
    vy
    vz
    @6
    @7
    cI
    cM
    frgpuptinv.m
    efgmval
    adantl
    fveq2d
    @6
    @18
    cT
    df-ov
    syl6eqr
    wph
    @10
    @11
    @19
    @17
    wceq
    #
    @11
    @7
    c0
    wceq
    #
    @7
    c1o
    wceq
    #
    wo
    #
    wph
    @10
    wa
    #
    @21
    @24
    @7
    c0
    c1o
    cpr
    #
    c2o
    @7
    c0
    c1o
    elpri
    df2o3
    eleq2s
    @25
    @22
    @21
    @23
    @25
    @21
    @22
    @6
    c1o
    cT
    co
    #
    @6
    c0
    cT
    co
    #
    cN
    cfv
    #
    wceq
    @25
    @27
    @6
    cF
    cfv
    #
    cN
    cfv
    #
    @29
    @25
    @10
    c1o
    c2o
    wcel
    @27
    @31
    wceq
    wph
    @10
    simpr
    #
    c1o
    @26
    c2o
    c0
    c1o
    c1o
    con0
    1on
    elexi
    prid2
    df2o3
    eleqtrri
    vy
    vz
    @6
    c1o
    cI
    c2o
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
    @36
    cN
    cfv
    #
    cif
    #
    @31
    cT
    @33
    c1o
    wceq
    #
    @35
    @6
    wceq
    #
    @38
    @37
    @31
    @39
    @33
    c0
    wne
    #
    @38
    @37
    wceq
    @39
    @41
    c1o
    c0
    wne
    1n0
    @33
    c1o
    c0
    neeq1
    mpbiri
    @33
    c0
    @36
    @37
    ifnefalse
    syl
    @40
    @36
    @30
    cN
    @35
    @6
    cF
    fveq2
    #
    fveq2d
    sylan9eqr
    frgpup.t
    @30
    cN
    fvex
    ovmpt2a
    sylancl
    @25
    @28
    @30
    cN
    @25
    @10
    c0
    c2o
    wcel
    @28
    @30
    wceq
    @32
    c0
    @26
    c2o
    c0
    c1o
    0ex
    prid1
    df2o3
    eleqtrri
    vy
    vz
    @6
    c0
    cI
    c2o
    @38
    @30
    cT
    @34
    @40
    @38
    @36
    @30
    @34
    @36
    @37
    iftrue
    @42
    sylan9eqr
    frgpup.t
    @6
    cF
    fvex
    ovmpt2a
    sylancl
    #
    fveq2d
    eqtr4d
    #
    @22
    @19
    @27
    @17
    @29
    @22
    @18
    c1o
    @6
    cT
    @22
    @18
    c1o
    c0
    cdif
    c1o
    @7
    c0
    c1o
    difeq2
    c1o
    dif0
    syl6eq
    oveq2d
    @22
    @16
    @28
    cN
    @7
    c0
    @6
    cT
    oveq2
    fveq2d
    eqeq12d
    syl5ibrcom
    @25
    @21
    @23
    @28
    @27
    cN
    cfv
    #
    wceq
    @25
    @45
    @29
    cN
    cfv
    #
    @28
    @25
    @27
    @29
    cN
    @44
    fveq2d
    @25
    cH
    cgrp
    wcel
    #
    @28
    cB
    wcel
    @46
    @28
    wceq
    wph
    @47
    @10
    frgpup.h
    adantr
    @25
    @28
    @30
    cB
    @43
    wph
    cI
    cB
    @6
    cF
    frgpup.a
    ffvelrnda
    eqeltrd
    cB
    cH
    cN
    @28
    frgpup.b
    frgpup.n
    grpinvinv
    syl2anc
    eqtr2d
    @23
    @19
    @28
    @17
    @45
    @23
    @18
    c0
    @6
    cT
    @23
    @18
    c1o
    c1o
    cdif
    c0
    @7
    c1o
    c1o
    difeq2
    c1o
    difid
    syl6eq
    oveq2d
    @23
    @16
    @27
    cN
    @7
    c1o
    @6
    cT
    oveq2
    fveq2d
    eqeq12d
    syl5ibrcom
    jaod
    syl5
    impr
    eqtrd
    @9
    @2
    @15
    @4
    @17
    @9
    @1
    @14
    cT
    @9
    @1
    @8
    cM
    cfv
    @14
    cA
    @8
    cM
    fveq2
    @6
    @7
    cM
    df-ov
    syl6eqr
    fveq2d
    @9
    @3
    @16
    cN
    @9
    @3
    @8
    cT
    cfv
    @16
    cA
    @8
    cT
    fveq2
    @6
    @7
    cT
    df-ov
    syl6eqr
    fveq2d
    eqeq12d
    syl5ibrcom
    rexlimdvva
    syl5bi
    imp
end
