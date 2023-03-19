include "wcel.mm"
include "crn.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "wn.mm"
include "gneispacern.mm"
include "neldifsnd.mm"
include "ssel.mm"
include "mtod.mm"
include "syl.mm"

theorem gneispace0nelrn3
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
  assert |- ( F e. A -> -. (/) e. ran F )

  proof
    cF
    cA
    wcel
    cF
    crn
    #
    cF
    cdm
    cpw
    c0
    csn
    #
    cdif
    cpw
    #
    @1
    cdif
    #
    wss
    #
    c0
    @0
    wcel
    #
    wn
    cA
    vf
    vn
    cF
    vs
    vp
    gneispace.a
    gneispacern
    @4
    @5
    c0
    @3
    wcel
    @4
    c0
    @2
    neldifsnd
    @0
    @3
    c0
    ssel
    mtod
    syl
end
