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
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "gneispace.mm"
include "syl.mm"
include "ibi.mm"
include "wfn.mm"
include "simp1.mm"
include "funfn.mm"
include "sylib.mm"
include "simp2.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem gneispacef2
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
  assert |- ( F e. A -> F : dom F --> ~P ~P dom F )

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
    #
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
    @7
    @6
    wcel
    wi
    vs
    @3
    wral
    wa
    vn
    @6
    wral
    wa
    vp
    @2
    wral
    #
    w3a
    #
    @2
    @4
    cF
    wf
    #
    @0
    @9
    @0
    cF
    cvv
    wcel
    @0
    @9
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
    @9
    cF
    @2
    wfn
    #
    @5
    @10
    @9
    @1
    @11
    @1
    @5
    @8
    simp1
    cF
    funfn
    sylib
    @1
    @5
    @8
    simp2
    @2
    @4
    cF
    df-f
    sylanbrc
    syl
end
