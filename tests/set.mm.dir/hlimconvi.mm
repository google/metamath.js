include "chli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "wcel.mm"
include "chil.mm"
include "wf.mm"
include "wa.mm"
include "hlimi.mm"
include "simprbi.mm"
include "wceq.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem hlimconvi
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  assume hlim.1: |- A e. _V

  disjoint y z
  disjoint F y
  disjoint F z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint f x
  disjoint F x
  disjoint w y
  disjoint f y
  disjoint w z
  disjoint f z
  disjoint f w
  disjoint F w
  disjoint F f
  disjoint A x
  disjoint A w
  disjoint A f
  disjoint B x
  assert |- ( ( F ~~>v A /\ B e. RR+ ) -> E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( F ` z ) -h A ) ) < B )

  proof
    cF
    cA
    chli
    wbr
    #
    vz
    cv
    cF
    cfv
    cA
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
    vy
    cv
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
    cB
    crp
    wcel
    @1
    cB
    clt
    wbr
    #
    vz
    @4
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
    cA
    chil
    wcel
    wa
    @6
    vx
    vy
    vz
    cA
    cF
    hlim.1
    hlimi
    simprbi
    @5
    @8
    vx
    cB
    crp
    @2
    cB
    wceq
    @3
    @7
    vy
    vz
    cn
    @4
    @2
    cB
    @1
    clt
    breq2
    rexralbidv
    rspccva
    sylan
end
