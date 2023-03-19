include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wss.mm"
include "wi.mm"
include "cdm.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "wfun.mm"
include "crn.mm"
include "w3a.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "gneispace.mm"
include "syl.mm"
include "ibi.mm"
include "simp3d.mm"
include "simpl.mm"
include "ralimi.mm"

theorem gneispace0nelrn
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let vs: setvar s
  let vp: setvar p
  let cP: class P
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
  assert |- ( F e. A -> A. p e. dom F ( F ` p ) =/= (/) )

  proof
    cF
    cA
    wcel
    #
    vp
    cv
    cF
    cfv
    #
    c0
    wne
    #
    vp
    vn
    wel
    vn
    cv
    vs
    cv
    #
    wss
    @3
    @1
    wcel
    wi
    vs
    cF
    cdm
    #
    cpw
    #
    wral
    wa
    vn
    @1
    wral
    #
    wa
    #
    vp
    @4
    wral
    #
    @2
    vp
    @4
    wral
    @0
    cF
    wfun
    #
    cF
    crn
    @5
    cpw
    wss
    #
    @8
    @0
    @9
    @10
    @8
    w3a
    #
    @0
    cF
    cvv
    wcel
    @0
    @11
    wb
    cF
    cA
    elex
    cA
    vf
    vn
    cF
    cvv
    vs
    vp
    gneispace.a
    gneispace
    syl
    ibi
    simp3d
    @7
    @2
    vp
    @4
    @2
    @6
    simpl
    ralimi
    syl
end
