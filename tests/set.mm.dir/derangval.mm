include "cv.mm"
include "wf1o.mm"
include "cfv.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "chash.mm"
include "cfn.mm"
include "wceq.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "raleq.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem derangval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let vf: setvar f
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
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
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
  disjoint V f
  assert |- ( A e. Fin -> ( D ` A ) = ( # ` { f | ( f : A -1-1-onto-> A /\ A. y e. A ( f ` y ) =/= y ) } ) )

  proof
    vx
    cA
    vx
    cv
    #
    @0
    vf
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @1
    cfv
    @3
    wne
    #
    vy
    @0
    wral
    #
    wa
    #
    vf
    cab
    #
    chash
    cfv
    cA
    cA
    @1
    wf1o
    #
    @4
    vy
    cA
    wral
    #
    wa
    #
    vf
    cab
    #
    chash
    cfv
    cfn
    cD
    @0
    cA
    wceq
    #
    @7
    @11
    chash
    @12
    @6
    @10
    vf
    @12
    @2
    @8
    @5
    @9
    @12
    @2
    cA
    @0
    @1
    wf1o
    @8
    @0
    cA
    @0
    @1
    f1oeq2
    @0
    cA
    cA
    @1
    f1oeq3
    bitrd
    @4
    vy
    @0
    cA
    raleq
    anbi12d
    abbidv
    fveq2d
    derang.d
    @11
    chash
    fvex
    fvmpt
end
