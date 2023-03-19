include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "chash.mm"
include "cn0.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "cfa.mm"
include "ceu.mm"
include "cdiv.mm"
include "c2.mm"
include "caddc.mm"
include "cfl.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "derangen2.mm"
include "adantr.mm"
include "cn.mm"
include "hashnncl.mm"
include "biimpar.mm"
include "subfacval3.mm"
include "syl.mm"
include "eqtrd.mm"

theorem derangfmla
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  assume derangfmla.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint f m
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint m n
  disjoint D m
  disjoint n x
  disjoint n y
  disjoint D n
  assert |- ( ( A e. Fin /\ A =/= (/) ) -> ( D ` A ) = ( |_ ` ( ( ( ! ` ( # ` A ) ) / _e ) + ( 1 / 2 ) ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cD
    cfv
    #
    cA
    chash
    cfv
    #
    vn
    cn0
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
    cmpt
    #
    cfv
    #
    @4
    cfa
    cfv
    ceu
    cdiv
    co
    c1
    c2
    cdiv
    co
    caddc
    co
    cfl
    cfv
    #
    @0
    @3
    @9
    wceq
    @1
    vx
    vy
    cA
    cD
    @8
    vf
    vm
    derangfmla.d
    vn
    vm
    cn0
    @7
    c1
    vm
    cv
    #
    cfz
    co
    #
    cD
    cfv
    @5
    @11
    wceq
    @6
    @12
    cD
    @5
    @11
    c1
    cfz
    oveq2
    fveq2d
    cbvmptv
    #
    derangen2
    adantr
    @2
    @4
    cn
    wcel
    #
    @9
    @10
    wceq
    @0
    @14
    @1
    cA
    hashnncl
    biimpar
    vx
    vy
    cD
    @8
    vf
    vm
    @4
    derangfmla.d
    @13
    subfacval3
    syl
    eqtrd
end
