include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "csb.mm"
include "wwe.mm"
include "wral.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "csbeq1d.mm"
include "fvex.mm"
include "csbie.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "rabbidv.mm"
include "weeq12d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "r19.21bi.mm"

theorem fnwe2lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
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
  let cB: class B
  assume fnwe2.su: |- ( z = ( F ` x ) -> S = U )
  assume fnwe2.t: |- T = { <. x , y >. | ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x U y ) ) }
  assume fnwe2.s: |- ( ( ph /\ x e. A ) -> U We { y e. A | ( F ` y ) = ( F ` x ) } )

  disjoint U y
  disjoint U z
  disjoint U a
  disjoint y z
  disjoint a y
  disjoint a z
  disjoint S x
  disjoint S y
  disjoint S a
  disjoint x y
  disjoint a x
  disjoint R x
  disjoint R y
  disjoint R a
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A a
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F a
  disjoint T a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint U e
  disjoint U f
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint a b
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
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S g
  disjoint b x
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
  disjoint R b
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
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  assert |- ( ( ph /\ a e. A ) -> [_ ( F ` a ) / z ]_ S We { y e. A | ( F ` y ) = ( F ` a ) } )

  proof
    wph
    vy
    cv
    cF
    cfv
    #
    va
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    cA
    crab
    #
    vz
    @2
    cS
    csb
    #
    wwe
    #
    va
    cA
    wph
    @0
    vx
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vy
    cA
    crab
    #
    cU
    wwe
    #
    vx
    cA
    wral
    @6
    va
    cA
    wral
    wph
    @11
    vx
    cA
    fnwe2.s
    ralrimiva
    @6
    @11
    va
    vx
    cA
    @1
    @7
    wceq
    #
    @4
    @10
    @5
    cU
    @12
    @5
    vz
    @8
    cS
    csb
    cU
    @12
    vz
    @2
    @8
    cS
    @1
    @7
    cF
    fveq2
    #
    csbeq1d
    vz
    @8
    cS
    cU
    @7
    cF
    fvex
    fnwe2.su
    csbie
    syl6eq
    @12
    @3
    @9
    vy
    cA
    @12
    @2
    @8
    @0
    @13
    eqeq2d
    rabbidv
    weeq12d
    cbvralv
    sylibr
    r19.21bi
end
