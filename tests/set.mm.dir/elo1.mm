include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cdm.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cc.mm"
include "cpm.mm"
include "co1.mm"
include "wceq.mm"
include "dmeq.mm"
include "ineq1d.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "2rexbidv.mm"
include "df-o1.mm"
include "elrab2.mm"

theorem elo1
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cF: class F
  let cA: class A
  let cC: class C
  let vf: setvar f
  let cM: class M

  disjoint m x
  disjoint m y
  disjoint x y
  disjoint F m
  disjoint F x
  disjoint F y
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint C m
  disjoint C x
  disjoint C y
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint M m
  disjoint M x
  assert |- ( F e. O(1) <-> ( F e. ( CC ^pm RR ) /\ E. x e. RR E. m e. RR A. y e. ( dom F i^i ( x [,) +oo ) ) ( abs ` ( F ` y ) ) <_ m ) )

  proof
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    cabs
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    vy
    @1
    cdm
    #
    vx
    cv
    cpnf
    cico
    co
    #
    cin
    #
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    @0
    cF
    cfv
    #
    cabs
    cfv
    #
    @4
    cle
    wbr
    #
    vy
    cF
    cdm
    #
    @7
    cin
    #
    wral
    #
    vm
    cr
    wrex
    vx
    cr
    wrex
    vf
    cF
    cc
    cr
    cpm
    co
    co1
    @1
    cF
    wceq
    #
    @9
    @15
    vx
    vm
    cr
    cr
    @16
    @5
    @12
    vy
    @8
    @14
    @16
    @6
    @13
    @7
    @1
    cF
    dmeq
    ineq1d
    @16
    @3
    @11
    @4
    cle
    @16
    @2
    @10
    cabs
    @0
    @1
    cF
    fveq1
    fveq2d
    breq1d
    raleqbidv
    2rexbidv
    vx
    vy
    vf
    vm
    df-o1
    elrab2
end
