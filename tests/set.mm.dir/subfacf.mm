include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cfv.mm"
include "cn0.mm"
include "wcel.mm"
include "wral.mm"
include "wf.mm"
include "cfn.mm"
include "fzfi.mm"
include "derangf.mm"
include "ffvelrni.mm"
include "ax-mp.mm"
include "rgenw.mm"
include "fmpt.mm"
include "mpbi.mm"

theorem subfacf
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vn: setvar n
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
  let cN: class N
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
  assert |- S : NN0 --> NN0

  proof
    c1
    vn
    cv
    #
    cfz
    co
    #
    cD
    cfv
    #
    cn0
    wcel
    #
    vn
    cn0
    wral
    cn0
    cn0
    cS
    wf
    @3
    vn
    cn0
    @1
    cfn
    wcel
    @3
    c1
    @0
    fzfi
    cfn
    cn0
    @1
    cD
    vx
    vy
    cD
    vf
    derang.d
    derangf
    ffvelrni
    ax-mp
    rgenw
    vn
    cn0
    cn0
    @2
    cS
    subfac.n
    fmpt
    mpbi
end
