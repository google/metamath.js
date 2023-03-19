include "wcel.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wel.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "gneispace2.mm"
include "ibi.mm"
include "simpr.mm"
include "2ralimi.mm"
include "simpl2im.mm"

theorem gneispacess
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
  assert |- ( F e. A -> A. p e. dom F A. n e. ( F ` p ) A. s e. ~P dom F ( n C_ s -> s e. ( F ` p ) ) )

  proof
    cF
    cA
    wcel
    #
    cF
    cdm
    #
    @1
    cpw
    #
    c0
    csn
    #
    cdif
    cpw
    @3
    cdif
    cF
    wf
    #
    vp
    vn
    wel
    #
    vn
    cv
    vs
    cv
    #
    wss
    @6
    vp
    cv
    cF
    cfv
    #
    wcel
    wi
    vs
    @2
    wral
    #
    wa
    #
    vn
    @7
    wral
    vp
    @1
    wral
    #
    @8
    vn
    @7
    wral
    vp
    @1
    wral
    @0
    @4
    @10
    wa
    cA
    vf
    vn
    cF
    cA
    vs
    vp
    gneispace.a
    gneispace2
    ibi
    @9
    @8
    vp
    vn
    @1
    @7
    @5
    @8
    simpr
    2ralimi
    simpl2im
end
