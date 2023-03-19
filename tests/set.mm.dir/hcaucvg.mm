include "ccau.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "chil.mm"
include "wf.mm"
include "hcau.mm"
include "simprbi.mm"
include "wceq.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem hcaucvg
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vf: setvar f

  disjoint y z
  disjoint F y
  disjoint F z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint f x
  disjoint F x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint A x
  assert |- ( ( F e. Cauchy /\ A e. RR+ ) -> E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( F ` y ) -h ( F ` z ) ) ) < A )

  proof
    cF
    ccau
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    vz
    cv
    cF
    cfv
    cmv
    co
    cno
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vz
    @1
    cuz
    cfv
    #
    wral
    vy
    cn
    wrex
    #
    vx
    crp
    wral
    #
    cA
    crp
    wcel
    @2
    cA
    clt
    wbr
    #
    vz
    @5
    wral
    vy
    cn
    wrex
    #
    @0
    cn
    chil
    cF
    wf
    @7
    vx
    vy
    vz
    cF
    hcau
    simprbi
    @6
    @9
    vx
    cA
    crp
    @3
    cA
    wceq
    @4
    @8
    vy
    vz
    cn
    @5
    @3
    cA
    @2
    clt
    breq2
    rexralbidv
    rspccva
    sylan
end
