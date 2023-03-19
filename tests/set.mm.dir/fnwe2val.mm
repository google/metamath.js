include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wo.mm"
include "csb.mm"
include "vex.mm"
include "fveq2.mm"
include "breqan12d.mm"
include "eqeqan12d.mm"
include "simpl.mm"
include "fvex.mm"
include "csbie.mm"
include "csbeq1d.mm"
include "syl5eqr.mm"
include "adantr.mm"
include "simpr.mm"
include "breq123d.mm"
include "anbi12d.mm"
include "orbi12d.mm"
include "braba.mm"

theorem fnwe2val
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume fnwe2.su: |- ( z = ( F ` x ) -> S = U )
  assume fnwe2.t: |- T = { <. x , y >. | ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x U y ) ) }

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
  disjoint x z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F a
  disjoint F b
  disjoint T a
  disjoint T b
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
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint g z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A a
  disjoint A b
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
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  assert |- ( a T b <-> ( ( F ` a ) R ( F ` b ) \/ ( ( F ` a ) = ( F ` b ) /\ a [_ ( F ` a ) / z ]_ S b ) ) )

  proof
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cR
    wbr
    #
    @1
    @3
    wceq
    #
    @0
    @2
    cU
    wbr
    #
    wa
    #
    wo
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
    @9
    @11
    wceq
    #
    @8
    @10
    vz
    @9
    cS
    csb
    #
    wbr
    #
    wa
    #
    wo
    vx
    vy
    @8
    @10
    cT
    va
    vex
    vb
    vex
    @0
    @8
    wceq
    #
    @2
    @10
    wceq
    #
    wa
    #
    @4
    @12
    @7
    @16
    @17
    @18
    @1
    @9
    @3
    @11
    cR
    @0
    @8
    cF
    fveq2
    #
    @2
    @10
    cF
    fveq2
    #
    breqan12d
    @19
    @5
    @13
    @6
    @15
    @17
    @18
    @1
    @9
    @3
    @11
    @20
    @21
    eqeqan12d
    @19
    @0
    @8
    @2
    @10
    cU
    @14
    @17
    @18
    simpl
    @17
    cU
    @14
    wceq
    @18
    @17
    cU
    vz
    @1
    cS
    csb
    @14
    vz
    @1
    cS
    cU
    @0
    cF
    fvex
    fnwe2.su
    csbie
    @17
    vz
    @1
    @9
    cS
    @20
    csbeq1d
    syl5eqr
    adantr
    @17
    @18
    simpr
    breq123d
    anbi12d
    orbi12d
    fnwe2.t
    braba
end
