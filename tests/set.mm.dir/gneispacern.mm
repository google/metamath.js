include "wcel.mm"
include "cdm.mm"
include "wfn.mm"
include "crn.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "wf.mm"
include "wa.mm"
include "gneispacef.mm"
include "df-f.mm"
include "sylib.mm"
include "simprd.mm"

theorem gneispacern
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
  assert |- ( F e. A -> ran F C_ ( ~P ( ~P dom F \ { (/) } ) \ { (/) } ) )

  proof
    cF
    cA
    wcel
    #
    cF
    cF
    cdm
    #
    wfn
    #
    cF
    crn
    @1
    cpw
    c0
    csn
    #
    cdif
    cpw
    @3
    cdif
    #
    wss
    #
    @0
    @1
    @4
    cF
    wf
    @2
    @5
    wa
    cA
    vf
    vn
    cF
    vs
    vp
    gneispace.a
    gneispacef
    @1
    @4
    cF
    df-f
    sylib
    simprd
end
