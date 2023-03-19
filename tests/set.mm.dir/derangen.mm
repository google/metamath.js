include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "derangenlem.mm"
include "ensym.mm"
include "adantr.mm"
include "enfi.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "cn0.mm"
include "wb.mm"
include "derangf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "adantl.mm"
include "cr.mm"
include "nn0re.mm"
include "letri3.mm"
include "syl2an.mm"
include "mpbir2and.mm"

theorem derangen
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
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
  disjoint B f
  disjoint B x
  disjoint B y
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
  disjoint B g
  disjoint B h
  disjoint B s
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
  assert |- ( ( A ~~ B /\ B e. Fin ) -> ( D ` A ) = ( D ` B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    cD
    cfv
    #
    cB
    cD
    cfv
    #
    wceq
    #
    @3
    @4
    cle
    wbr
    #
    @4
    @3
    cle
    wbr
    #
    vx
    vy
    cA
    cB
    cD
    vf
    derang.d
    derangenlem
    @2
    cB
    cA
    cen
    wbr
    #
    cA
    cfn
    wcel
    #
    @7
    @0
    @8
    @1
    cA
    cB
    ensym
    adantr
    @0
    @9
    @1
    cA
    cB
    enfi
    biimpar
    #
    vx
    vy
    cB
    cA
    cD
    vf
    derang.d
    derangenlem
    syl2anc
    @2
    @3
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    @5
    @6
    @7
    wa
    wb
    #
    @2
    @9
    @11
    @10
    cfn
    cn0
    cA
    cD
    vx
    vy
    cD
    vf
    derang.d
    derangf
    #
    ffvelrni
    syl
    @1
    @12
    @0
    cfn
    cn0
    cB
    cD
    @14
    ffvelrni
    adantl
    @11
    @3
    cr
    wcel
    @4
    cr
    wcel
    @13
    @12
    @3
    nn0re
    @4
    nn0re
    @3
    @4
    letri3
    syl2an
    syl2anc
    mpbir2and
end
