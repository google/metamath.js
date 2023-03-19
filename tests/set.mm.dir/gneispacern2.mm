include "wcel.mm"
include "wfun.mm"
include "crn.mm"
include "cdm.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "gneispace.mm"
include "syl.mm"
include "ibi.mm"
include "simp2d.mm"

theorem gneispacern2
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
  assert |- ( F e. A -> ran F C_ ~P ~P dom F )

  proof
    cF
    cA
    wcel
    #
    cF
    wfun
    #
    cF
    crn
    cF
    cdm
    #
    cpw
    #
    cpw
    wss
    #
    vp
    cv
    cF
    cfv
    #
    c0
    wne
    vp
    vn
    wel
    vn
    cv
    vs
    cv
    #
    wss
    @6
    @5
    wcel
    wi
    vs
    @3
    wral
    wa
    vn
    @5
    wral
    wa
    vp
    @2
    wral
    #
    @0
    @1
    @4
    @7
    w3a
    #
    @0
    cF
    cvv
    wcel
    @0
    @8
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
    simp2d
end
