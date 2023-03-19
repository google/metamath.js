include "wfr.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wwe.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "adantlr.mm"
include "cres.mm"
include "wf.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "fnwe2lem2.mm"
include "ex.mm"
include "alrimiv.mm"
include "df-fr.mm"
include "sylibr.mm"
include "fnwe2lem3.mm"
include "ralrimivva.mm"
include "dfwe2.mm"
include "sylanbrc.mm"

theorem fnwe2
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

  disjoint U y
  disjoint U z
  disjoint y z
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint U e
  disjoint U f
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint a z
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
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S g
  disjoint a x
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
  disjoint R a
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
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint T a
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
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> T We A )

  proof
    wph
    cA
    cT
    wfr
    #
    va
    cv
    #
    vb
    cv
    #
    cT
    wbr
    va
    vb
    weq
    @2
    @1
    cT
    wbr
    w3o
    #
    vb
    cA
    wral
    va
    cA
    wral
    cA
    cT
    wwe
    wph
    @1
    cA
    wss
    #
    @1
    c0
    wne
    #
    wa
    #
    vd
    cv
    vc
    cv
    cT
    wbr
    wn
    vd
    @1
    wral
    vc
    @1
    wrex
    #
    wi
    #
    va
    wal
    @0
    wph
    @8
    va
    wph
    @6
    @7
    wph
    @6
    wa
    vx
    vy
    vz
    cA
    cB
    cR
    cS
    cT
    cU
    cF
    va
    vc
    vd
    fnwe2.su
    fnwe2.t
    wph
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    cF
    cfv
    @9
    cF
    cfv
    wceq
    vy
    cA
    crab
    cU
    wwe
    #
    @6
    fnwe2.s
    adantlr
    wph
    cA
    cB
    cF
    cA
    cres
    wf
    #
    @6
    fnwe2.f
    adantr
    wph
    cB
    cR
    wwe
    #
    @6
    fnwe2.r
    adantr
    wph
    @4
    @5
    simprl
    wph
    @4
    @5
    simprr
    fnwe2lem2
    ex
    alrimiv
    va
    vc
    vd
    cA
    cT
    df-fr
    sylibr
    wph
    @3
    va
    vb
    cA
    cA
    wph
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    #
    wa
    vx
    vy
    vz
    cA
    cB
    cR
    cS
    cT
    cU
    cF
    va
    vb
    fnwe2.su
    fnwe2.t
    wph
    @10
    @11
    @16
    fnwe2.s
    adantlr
    wph
    @12
    @16
    fnwe2.f
    adantr
    wph
    @13
    @16
    fnwe2.r
    adantr
    wph
    @14
    @15
    simprl
    wph
    @14
    @15
    simprr
    fnwe2lem3
    ralrimivva
    va
    vb
    cA
    cT
    dfwe2
    sylanbrc
end
