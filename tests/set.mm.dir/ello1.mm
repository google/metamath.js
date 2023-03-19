include "cv.mm"
include "cfv.mm"
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
include "cpm.mm"
include "clo1.mm"
include "wceq.mm"
include "dmeq.mm"
include "ineq1d.mm"
include "fveq1.mm"
include "breq1d.mm"
include "raleqbidv.mm"
include "2rexbidv.mm"
include "df-lo1.mm"
include "elrab2.mm"

theorem ello1
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
  assert |- ( F e. <_O(1) <-> ( F e. ( RR ^pm RR ) /\ E. x e. RR E. m e. RR A. y e. ( dom F i^i ( x [,) +oo ) ) ( F ` y ) <_ m ) )

  proof
    vy
    cv
    #
    vf
    cv
    #
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
    @3
    cle
    wbr
    #
    vy
    cF
    cdm
    #
    @6
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
    cr
    cr
    cpm
    co
    clo1
    @1
    cF
    wceq
    #
    @8
    @13
    vx
    vm
    cr
    cr
    @14
    @4
    @10
    vy
    @7
    @12
    @14
    @5
    @11
    @6
    @1
    cF
    dmeq
    ineq1d
    @14
    @2
    @9
    @3
    cle
    @0
    @1
    cF
    fveq1
    breq1d
    raleqbidv
    2rexbidv
    vx
    vy
    vf
    vm
    df-lo1
    elrab2
end
