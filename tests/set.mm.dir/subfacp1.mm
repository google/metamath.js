include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "cfv.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "weq.mm"
include "f1oeq1.mm"
include "fveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "cbvralv.mm"
include "fveq1.mm"
include "neeq1d.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "cbvabv.mm"
include "subfacp1lem6.mm"

theorem subfacp1
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cB: class B
  let cC: class C
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N f
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint D n
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
  disjoint A f
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
  disjoint n z
  disjoint A n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
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
  disjoint V f
  assert |- ( N e. NN -> ( S ` ( N + 1 ) ) = ( N x. ( ( S ` N ) + ( S ` ( N - 1 ) ) ) ) )

  proof
    vx
    vy
    c1
    cN
    c1
    caddc
    co
    cfz
    co
    #
    @0
    vg
    cv
    #
    wf1o
    #
    vz
    cv
    #
    @1
    cfv
    #
    @3
    wne
    #
    vz
    @0
    wral
    #
    wa
    #
    vg
    cab
    cD
    cS
    vf
    vn
    cN
    derang.d
    subfac.n
    @7
    @0
    @0
    vf
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @8
    cfv
    #
    @10
    wne
    #
    vy
    @0
    wral
    #
    wa
    vg
    vf
    vg
    vf
    weq
    #
    @2
    @9
    @6
    @13
    @0
    @0
    @1
    @8
    f1oeq1
    @6
    @10
    @1
    cfv
    #
    @10
    wne
    #
    vy
    @0
    wral
    @14
    @13
    @5
    @16
    vz
    vy
    @0
    vz
    vy
    weq
    #
    @4
    @15
    @3
    @10
    @3
    @10
    @1
    fveq2
    @17
    id
    neeq12d
    cbvralv
    @14
    @16
    @12
    vy
    @0
    @14
    @15
    @11
    @10
    @10
    @1
    @8
    fveq1
    neeq1d
    ralbidv
    syl5bb
    anbi12d
    cbvabv
    subfacp1lem6
end
