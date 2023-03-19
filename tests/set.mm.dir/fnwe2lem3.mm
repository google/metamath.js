include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wceq.mm"
include "wa.mm"
include "csb.mm"
include "wo.mm"
include "orc.mm"
include "adantl.mm"
include "fnwe2val.mm"
include "sylibr.mm"
include "3mix1d.mm"
include "simplr.mm"
include "simpr.mm"
include "jca.mm"
include "olcd.mm"
include "3mix2.mm"
include "eqcomd.mm"
include "csbeq1.mm"
include "breqd.mm"
include "biimpa.mm"
include "3mix3d.mm"
include "crab.mm"
include "wor.mm"
include "wcel.mm"
include "wwe.mm"
include "fnwe2lem1.mm"
include "mpdan.mm"
include "weso.mm"
include "syl.mm"
include "adantr.mm"
include "eqidd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "solin.mm"
include "syl12anc.mm"
include "mpjao3dan.mm"
include "cres.mm"
include "fvres.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"

theorem fnwe2lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  assume fnwe2.su: |- ( z = ( F ` x ) -> S = U )
  assume fnwe2.t: |- T = { <. x , y >. | ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x U y ) ) }
  assume fnwe2.s: |- ( ( ph /\ x e. A ) -> U We { y e. A | ( F ` y ) = ( F ` x ) } )
  assume fnwe2.f: |- ( ph -> ( F |` A ) : A --> B )
  assume fnwe2.r: |- ( ph -> R We B )
  assume fnwe2lem3.a: |- ( ph -> a e. A )
  assume fnwe2lem3.b: |- ( ph -> b e. A )

  disjoint U y
  disjoint U z
  disjoint U a
  disjoint U b
  disjoint y z
  disjoint a y
  disjoint b y
  disjoint a z
  disjoint b z
  disjoint a b
  disjoint S x
  disjoint S y
  disjoint S a
  disjoint S b
  disjoint x y
  disjoint a x
  disjoint b x
  disjoint R x
  disjoint R y
  disjoint R a
  disjoint R b
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A a
  disjoint A b
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F a
  disjoint F b
  disjoint T a
  disjoint T b
  disjoint B a
  disjoint B b
  disjoint U c
  disjoint U d
  disjoint U e
  disjoint U f
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S g
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint g x
  disjoint g y
  disjoint a g
  disjoint b g
  disjoint c g
  disjoint d g
  disjoint e g
  disjoint f g
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint g z
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint T c
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  assert |- ( ph -> ( a T b \/ a = b \/ b T a ) )

  proof
    wph
    va
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cF
    cfv
    #
    cR
    wbr
    #
    @0
    @2
    cT
    wbr
    #
    va
    vb
    weq
    #
    @2
    @0
    cT
    wbr
    #
    w3o
    #
    @1
    @3
    wceq
    #
    @3
    @1
    cR
    wbr
    #
    wph
    @4
    wa
    #
    @5
    @6
    @7
    @11
    @4
    @9
    @0
    @2
    vz
    @1
    cS
    csb
    #
    wbr
    #
    wa
    #
    wo
    #
    @5
    @4
    @15
    wph
    @4
    @14
    orc
    adantl
    vx
    vy
    vz
    cR
    cS
    cT
    cU
    cF
    va
    vb
    fnwe2.su
    fnwe2.t
    fnwe2val
    #
    sylibr
    3mix1d
    wph
    @9
    wa
    #
    @13
    @8
    @6
    @2
    @0
    @12
    wbr
    #
    @17
    @13
    wa
    #
    @5
    @6
    @7
    @19
    @15
    @5
    @19
    @14
    @4
    @19
    @9
    @13
    wph
    @9
    @13
    simplr
    @17
    @13
    simpr
    jca
    olcd
    @16
    sylibr
    3mix1d
    @6
    @8
    @17
    @6
    @5
    @7
    3mix2
    adantl
    @17
    @18
    wa
    #
    @7
    @5
    @6
    @20
    @10
    @3
    @1
    wceq
    #
    @2
    @0
    vz
    @3
    cS
    csb
    #
    wbr
    #
    wa
    #
    wo
    #
    @7
    @20
    @24
    @10
    @20
    @21
    @23
    @20
    @1
    @3
    wph
    @9
    @18
    simplr
    eqcomd
    @17
    @18
    @23
    @17
    @12
    @22
    @2
    @0
    @9
    @12
    @22
    wceq
    wph
    vz
    @1
    @3
    cS
    csbeq1
    adantl
    breqd
    biimpa
    jca
    olcd
    vx
    vy
    vz
    cR
    cS
    cT
    cU
    cF
    vb
    va
    fnwe2.su
    fnwe2.t
    fnwe2val
    #
    sylibr
    3mix3d
    @17
    vy
    cv
    #
    cF
    cfv
    #
    @1
    wceq
    #
    vy
    cA
    crab
    #
    @12
    wor
    #
    @0
    @30
    wcel
    #
    @2
    @30
    wcel
    #
    @13
    @6
    @18
    w3o
    wph
    @31
    @9
    wph
    @30
    @12
    wwe
    #
    @31
    wph
    @0
    cA
    wcel
    #
    @34
    fnwe2lem3.a
    wph
    vx
    vy
    vz
    cA
    cR
    cS
    cT
    cU
    cF
    va
    fnwe2.su
    fnwe2.t
    fnwe2.s
    fnwe2lem1
    mpdan
    @30
    @12
    weso
    syl
    adantr
    @17
    @35
    @1
    @1
    wceq
    #
    @32
    wph
    @35
    @9
    fnwe2lem3.a
    adantr
    @17
    @1
    eqidd
    @29
    @36
    vy
    @0
    cA
    vy
    va
    weq
    @28
    @1
    @1
    @27
    @0
    cF
    fveq2
    eqeq1d
    elrab
    sylanbrc
    @17
    @2
    cA
    wcel
    #
    @21
    @33
    wph
    @37
    @9
    fnwe2lem3.b
    adantr
    @17
    @1
    @3
    wph
    @9
    simpr
    eqcomd
    @29
    @21
    vy
    @2
    cA
    vy
    vb
    weq
    @28
    @3
    @1
    @27
    @2
    cF
    fveq2
    eqeq1d
    elrab
    sylanbrc
    @30
    @0
    @2
    @12
    solin
    syl12anc
    mpjao3dan
    wph
    @10
    wa
    #
    @7
    @5
    @6
    @38
    @25
    @7
    @10
    @25
    wph
    @10
    @24
    orc
    adantl
    @26
    sylibr
    3mix3d
    wph
    cB
    cR
    wor
    #
    @1
    cB
    wcel
    @3
    cB
    wcel
    @4
    @9
    @10
    w3o
    wph
    cB
    cR
    wwe
    @39
    fnwe2.r
    cB
    cR
    weso
    syl
    wph
    @0
    cF
    cA
    cres
    #
    cfv
    #
    @1
    cB
    wph
    @35
    @41
    @1
    wceq
    fnwe2lem3.a
    @0
    cA
    cF
    fvres
    syl
    wph
    cA
    cB
    @0
    @40
    fnwe2.f
    fnwe2lem3.a
    ffvelrnd
    eqeltrrd
    wph
    @2
    @40
    cfv
    #
    @3
    cB
    wph
    @37
    @42
    @3
    wceq
    fnwe2lem3.b
    @2
    cA
    cF
    fvres
    syl
    wph
    cA
    cB
    @2
    @40
    fnwe2.f
    fnwe2lem3.b
    ffvelrnd
    eqeltrrd
    cB
    @1
    @3
    cR
    solin
    syl12anc
    mpjao3dan
end
