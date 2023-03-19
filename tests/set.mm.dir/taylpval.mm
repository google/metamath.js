include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvn.mm"
include "cfv.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cc.mm"
include "cvv.mm"
include "taylpfval.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "simplr.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"
include "sumex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem taylpval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  assume taylpfval.s: |- ( ph -> S e. { RR , CC } )
  assume taylpfval.f: |- ( ph -> F : A --> CC )
  assume taylpfval.a: |- ( ph -> A C_ S )
  assume taylpfval.n: |- ( ph -> N e. NN0 )
  assume taylpfval.b: |- ( ph -> B e. dom ( ( S Dn F ) ` N ) )
  assume taylpfval.t: |- T = ( N ( S Tayl F ) B )
  assume taylpval.x: |- ( ph -> X e. CC )

  disjoint B k
  disjoint F k
  disjoint N k
  disjoint k ph
  disjoint S k
  disjoint X k
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint D k
  disjoint D u
  disjoint D v
  disjoint D y
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint X x
  assert |- ( ph -> ( T ` X ) = sum_ k e. ( 0 ... N ) ( ( ( ( ( S Dn F ) ` k ) ` B ) / ( ! ` k ) ) x. ( ( X - B ) ^ k ) ) )

  proof
    wph
    vx
    cX
    cc0
    cN
    cfz
    co
    #
    cB
    vk
    cv
    #
    cS
    cF
    cdvn
    co
    cfv
    cfv
    @1
    cfa
    cfv
    cdiv
    co
    #
    vx
    cv
    #
    cB
    cmin
    co
    #
    @1
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    @0
    @2
    cX
    cB
    cmin
    co
    #
    @1
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cc
    cT
    cvv
    wph
    vx
    cA
    cB
    cS
    cT
    vk
    cF
    cN
    taylpfval.s
    taylpfval.f
    taylpfval.a
    taylpfval.n
    taylpfval.b
    taylpfval.t
    taylpfval
    wph
    @3
    cX
    wceq
    #
    wa
    #
    @0
    @6
    @9
    vk
    @12
    @1
    @0
    wcel
    #
    wa
    #
    @5
    @8
    @2
    cmul
    @14
    @4
    @7
    @1
    cexp
    @14
    @3
    cX
    cB
    cmin
    wph
    @11
    @13
    simplr
    oveq1d
    oveq1d
    oveq2d
    sumeq2dv
    taylpval.x
    @10
    cvv
    wcel
    wph
    @0
    @9
    vk
    sumex
    a1i
    fvmptd
end
