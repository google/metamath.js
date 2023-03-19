include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wf1o.mm"
include "cfv.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "chash.mm"
include "cfa.mm"
include "cle.mm"
include "wbr.mm"
include "cdom.mm"
include "cfn.mm"
include "wss.mm"
include "anidm.mm"
include "abbii.mm"
include "fzfid.mm"
include "deranglem.mm"
include "syl.mm"
include "syl5eqelr.mm"
include "simpl.mm"
include "ss2abi.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "wb.mm"
include "hashdom.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "subfacval.mm"
include "wceq.mm"
include "derangval.mm"
include "eqtrd.mm"
include "hashfac.mm"
include "hashfz1.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "3brtr4d.mm"

theorem subfaclefac
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
  assert |- ( N e. NN0 -> ( S ` N ) <_ ( ! ` N ) )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    @1
    vf
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @2
    cfv
    @4
    wne
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
    vf
    cab
    #
    chash
    cfv
    #
    cN
    cS
    cfv
    #
    cN
    cfa
    cfv
    #
    cle
    @0
    @8
    @10
    cle
    wbr
    #
    @7
    @9
    cdom
    wbr
    #
    @0
    @9
    cfn
    wcel
    #
    @7
    @9
    wss
    @14
    @0
    @9
    @3
    @3
    wa
    #
    vf
    cab
    #
    cfn
    @16
    @3
    vf
    @3
    anidm
    abbii
    @0
    @1
    cfn
    wcel
    #
    @17
    cfn
    wcel
    @0
    c1
    cN
    fzfid
    #
    @3
    @1
    vf
    deranglem
    syl
    syl5eqelr
    #
    @6
    @3
    vf
    @3
    @5
    simpl
    ss2abi
    @7
    @9
    cfn
    ssdomg
    mpisyl
    @0
    @7
    cfn
    wcel
    #
    @15
    @13
    @14
    wb
    @0
    @18
    @21
    @19
    @5
    @1
    vf
    deranglem
    syl
    @20
    @7
    @9
    cfn
    hashdom
    syl2anc
    mpbird
    @0
    @11
    @1
    cD
    cfv
    #
    @8
    vx
    vy
    cD
    cS
    vf
    vn
    cN
    derang.d
    subfac.n
    subfacval
    @0
    @18
    @22
    @8
    wceq
    @19
    vx
    vy
    @1
    cD
    vf
    derang.d
    derangval
    syl
    eqtrd
    @0
    @10
    @1
    chash
    cfv
    #
    cfa
    cfv
    #
    @12
    @0
    @18
    @10
    @24
    wceq
    @19
    @1
    vf
    hashfac
    syl
    @0
    @23
    cN
    cfa
    cN
    hashfz1
    fveq2d
    eqtr2d
    3brtr4d
end
