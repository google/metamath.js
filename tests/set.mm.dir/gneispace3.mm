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
include "wfun.mm"
include "crn.mm"
include "gneispace2.mm"
include "wfn.mm"
include "df-f.mm"
include "funfn.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem gneispace3
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  assume gneispace.a: |- A = { f | ( f : dom f --> ( ~P ( ~P dom f \ { (/) } ) \ { (/) } ) /\ A. p e. dom f A. n e. ( f ` p ) ( p e. n /\ A. s e. ~P dom f ( n C_ s -> s e. ( f ` p ) ) ) ) }

  disjoint F n
  disjoint F p
  disjoint n p
  disjoint F f
  disjoint F s
  disjoint f s
  disjoint f n
  disjoint f p
  assert |- ( F e. V -> ( F e. A <-> ( ( Fun F /\ ran F C_ ( ~P ( ~P dom F \ { (/) } ) \ { (/) } ) ) /\ A. p e. dom F A. n e. ( F ` p ) ( p e. n /\ A. s e. ~P dom F ( n C_ s -> s e. ( F ` p ) ) ) ) ) )

  proof
    cF
    cV
    wcel
    cF
    cA
    wcel
    cF
    cdm
    #
    @0
    cpw
    #
    c0
    csn
    #
    cdif
    cpw
    @2
    cdif
    #
    cF
    wf
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
    @5
    vp
    cv
    cF
    cfv
    #
    wcel
    wi
    vs
    @1
    wral
    wa
    vn
    @6
    wral
    vp
    @0
    wral
    #
    wa
    cF
    wfun
    #
    cF
    crn
    @3
    wss
    #
    wa
    #
    @7
    wa
    cA
    vf
    vn
    cF
    cV
    vs
    vp
    gneispace.a
    gneispace2
    @4
    @10
    @7
    @4
    cF
    @0
    wfn
    #
    @9
    wa
    @10
    @0
    @3
    cF
    df-f
    @8
    @11
    @9
    cF
    funfn
    anbi1i
    bitr4i
    anbi1i
    syl6bb
end
