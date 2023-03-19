include "wcel.mm"
include "wa.mm"
include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wf1o.mm"
include "subfacp1lem2a.mm"
include "simp1d.mm"
include "f1ofun.mm"
include "syl.mm"
include "adantr.mm"
include "cop.mm"
include "cpr.mm"
include "cun.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "f1odm.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "funssfv.mm"
include "syl3anc.mm"

theorem subfacp1lem2b
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let cB: class B
  let cC: class C
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )
  assume subfacp1lem.a: |- A = { f | ( f : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\ A. y e. ( 1 ... ( N + 1 ) ) ( f ` y ) =/= y ) }
  assume subfacp1lem1.n: |- ( ph -> N e. NN )
  assume subfacp1lem1.m: |- ( ph -> M e. ( 2 ... ( N + 1 ) ) )
  assume subfacp1lem1.x: |- M e. _V
  assume subfacp1lem1.k: |- K = ( ( 2 ... ( N + 1 ) ) \ { M } )
  assume subfacp1lem2.5: |- F = ( G u. { <. 1 , M >. , <. M , 1 >. } )
  assume subfacp1lem2.6: |- ( ph -> G : K -1-1-onto-> K )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint N f
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint D n
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M f
  disjoint M x
  disjoint M y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f g
  disjoint f h
  disjoint f m
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
  disjoint n z
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
  disjoint F g
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
  disjoint K c
  disjoint M b
  disjoint M g
  disjoint S m
  disjoint V f
  assert |- ( ( ph /\ X e. K ) -> ( F ` X ) = ( G ` X ) )

  proof
    wph
    cX
    cK
    wcel
    #
    wa
    #
    cF
    wfun
    #
    cG
    cF
    wss
    #
    cX
    cG
    cdm
    #
    wcel
    #
    cX
    cF
    cfv
    cX
    cG
    cfv
    wceq
    wph
    @2
    @0
    wph
    c1
    cN
    c1
    caddc
    co
    cfz
    co
    #
    @6
    cF
    wf1o
    #
    @2
    wph
    @7
    c1
    cF
    cfv
    cM
    wceq
    cM
    cF
    cfv
    c1
    wceq
    wph
    vx
    vy
    cA
    cD
    cS
    vf
    vn
    cF
    cG
    cK
    cM
    cN
    derang.d
    subfac.n
    subfacp1lem.a
    subfacp1lem1.n
    subfacp1lem1.m
    subfacp1lem1.x
    subfacp1lem1.k
    subfacp1lem2.5
    subfacp1lem2.6
    subfacp1lem2a
    simp1d
    @6
    @6
    cF
    f1ofun
    syl
    adantr
    @3
    @1
    cG
    cG
    c1
    cM
    cop
    cM
    c1
    cop
    cpr
    #
    cun
    cF
    cG
    @8
    ssun1
    subfacp1lem2.5
    sseqtr4i
    a1i
    wph
    @5
    @0
    wph
    @4
    cK
    cX
    wph
    cK
    cK
    cG
    wf1o
    @4
    cK
    wceq
    subfacp1lem2.6
    cK
    cK
    cG
    f1odm
    syl
    eleq2d
    biimpar
    cX
    cF
    cG
    funssfv
    syl3anc
end
