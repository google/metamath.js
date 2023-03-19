include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "c0.mm"
include "chash.mm"
include "cc0.mm"
include "cv.mm"
include "wf1o.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "cfn.mm"
include "wceq.mm"
include "snfi.mm"
include "derangval.mm"
include "ax-mp.mm"
include "wss.mm"
include "wf.mm"
include "f1of.mm"
include "adantr.mm"
include "snidg.mm"
include "ffvelrn.mm"
include "syl2anr.mm"
include "wn.mm"
include "simpr.mm"
include "fveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "rspcva.mm"
include "syl2an.mm"
include "nelsn.mm"
include "syl.mm"
include "pm2.21dd.mm"
include "ex.mm"
include "abssdv.mm"
include "ss0.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "hash0.mm"
include "syl6eq.mm"

theorem derangsn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let vf: setvar f
  let cV: class V
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cN: class N
  let cB: class B
  let cC: class C
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cS: class S
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint V f
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f z
  disjoint g h
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint f k
  disjoint N f
  disjoint g k
  disjoint N g
  disjoint h k
  disjoint N h
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b h
  disjoint b s
  disjoint b z
  disjoint B b
  disjoint c s
  disjoint B c
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint b ph
  disjoint c ph
  disjoint ph x
  disjoint ph y
  disjoint D n
  disjoint K c
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  assert |- ( A e. V -> ( D ` { A } ) = 0 )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
    cD
    cfv
    #
    c0
    chash
    cfv
    #
    cc0
    @0
    @2
    @1
    @1
    vf
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @4
    cfv
    #
    @6
    wne
    #
    vy
    @1
    wral
    #
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    @3
    @1
    cfn
    wcel
    @2
    @12
    wceq
    cA
    snfi
    vx
    vy
    @1
    cD
    vf
    derang.d
    derangval
    ax-mp
    @0
    @11
    c0
    chash
    @0
    @11
    c0
    wss
    @11
    c0
    wceq
    @0
    @10
    vf
    c0
    @0
    @10
    @4
    c0
    wcel
    #
    @0
    @10
    wa
    #
    cA
    @4
    cfv
    #
    @1
    wcel
    #
    @13
    @10
    @1
    @1
    @4
    wf
    #
    cA
    @1
    wcel
    #
    @16
    @0
    @5
    @17
    @9
    @1
    @1
    @4
    f1of
    adantr
    cA
    cV
    snidg
    #
    @1
    @1
    cA
    @4
    ffvelrn
    syl2anr
    @14
    @15
    cA
    wne
    #
    @16
    wn
    @0
    @18
    @9
    @20
    @10
    @19
    @5
    @9
    simpr
    @8
    @20
    vy
    cA
    @1
    @6
    cA
    wceq
    #
    @7
    @15
    @6
    cA
    @6
    cA
    @4
    fveq2
    @21
    id
    neeq12d
    rspcva
    syl2an
    @15
    cA
    nelsn
    syl
    pm2.21dd
    ex
    abssdv
    @11
    ss0
    syl
    fveq2d
    syl5eq
    hash0
    syl6eq
end
