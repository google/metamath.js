include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "wa.mm"
include "cab.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "mapfi.mm"
include "wf.mm"
include "f1of.mm"
include "adantr.mm"
include "elmapg.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "anidms.mm"

theorem deranglem
  let wph: wff ph
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cN: class N
  let cB: class B
  let cC: class C
  let cD: class D
  let cK: class K
  let cM: class M
  let cS: class S
  let cV: class V

  disjoint A f
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f x
  disjoint f y
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
  disjoint x y
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
  assert |- ( A e. Fin -> { f | ( f : A -1-1-onto-> A /\ ph ) } e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cA
    cA
    vf
    cv
    #
    wf1o
    #
    wph
    wa
    #
    vf
    cab
    #
    cfn
    wcel
    #
    @0
    @0
    wa
    #
    cA
    cA
    cmap
    co
    #
    cfn
    wcel
    @4
    @7
    wss
    @5
    cA
    cA
    mapfi
    @6
    @3
    vf
    @7
    @3
    @1
    @7
    wcel
    @6
    cA
    cA
    @1
    wf
    #
    @2
    @8
    wph
    cA
    cA
    @1
    f1of
    adantr
    cA
    cA
    @1
    cfn
    cfn
    elmapg
    syl5ibr
    abssdv
    @7
    @4
    ssfi
    syl2anc
    anidms
end
