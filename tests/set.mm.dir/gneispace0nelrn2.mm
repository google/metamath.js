include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "gneispace0nelrn.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "rspccv.mm"
include "syl.mm"
include "imp.mm"

theorem gneispace0nelrn2
  let cA: class A
  let cP: class P
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let vs: setvar s
  let vp: setvar p
  let cN: class N
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
  assert |- ( ( F e. A /\ P e. dom F ) -> ( F ` P ) =/= (/) )

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
    cP
    cF
    cfv
    #
    c0
    wne
    #
    @0
    vp
    cv
    #
    cF
    cfv
    #
    c0
    wne
    #
    vp
    @1
    wral
    @2
    @4
    wi
    cA
    vf
    vn
    cF
    vs
    vp
    gneispace.a
    gneispace0nelrn
    @7
    @4
    vp
    cP
    @1
    @5
    cP
    wceq
    @6
    @3
    c0
    @5
    cP
    cF
    fveq2
    neeq1d
    rspccv
    syl
    imp
end
