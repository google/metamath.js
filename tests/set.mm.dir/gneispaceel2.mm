include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "wel.mm"
include "gneispaceel.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1.mm"
include "raleqbidv.mm"
include "rspccv.mm"
include "syl.mm"
include "eleq2.mm"
include "syl6.mm"
include "3imp.mm"

theorem gneispaceel2
  let cA: class A
  let cP: class P
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vs: setvar s
  let vp: setvar p
  let cS: class S
  assume gneispace.a: |- A = { f | ( f : dom f --> ( ~P ( ~P dom f \ { (/) } ) \ { (/) } ) /\ A. p e. dom f A. n e. ( f ` p ) ( p e. n /\ A. s e. ~P dom f ( n C_ s -> s e. ( f ` p ) ) ) ) }

  disjoint F n
  disjoint F p
  disjoint n p
  disjoint F f
  disjoint F s
  disjoint f s
  disjoint f n
  disjoint f p
  disjoint P p
  disjoint P n
  disjoint N n
  disjoint S s
  assert |- ( ( F e. A /\ P e. dom F /\ N e. ( F ` P ) ) -> P e. N )

  proof
    cF
    cA
    wcel
    #
    cP
    cF
    cdm
    #
    wcel
    #
    cN
    cP
    cF
    cfv
    #
    wcel
    #
    cP
    cN
    wcel
    #
    @0
    @2
    cP
    vn
    cv
    #
    wcel
    #
    vn
    @3
    wral
    #
    @4
    @5
    wi
    @0
    vp
    vn
    wel
    #
    vn
    vp
    cv
    #
    cF
    cfv
    #
    wral
    #
    vp
    @1
    wral
    @2
    @8
    wi
    cA
    vf
    vn
    cF
    vs
    vp
    gneispace.a
    gneispaceel
    @12
    @8
    vp
    cP
    @1
    @10
    cP
    wceq
    @9
    @7
    vn
    @11
    @3
    @10
    cP
    cF
    fveq2
    @10
    cP
    @6
    eleq1
    raleqbidv
    rspccv
    syl
    @7
    @5
    vn
    cN
    @3
    @6
    cN
    cP
    eleq2
    rspccv
    syl6
    3imp
end
