include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cuni.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wn.mm"
include "wf.mm"
include "cfv.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "uniex.mm"
include "numth3.mm"
include "mp1i.mm"
include "neirr.mm"
include "neeq1.mm"
include "rspccv.mm"
include "mtoi.mm"
include "ac5num.mm"
include "syl2anc.mm"

theorem ac5b
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  assume ac5b.1: |- A e. _V

  disjoint f x
  disjoint A x
  disjoint A f
  assert |- ( A. x e. A x =/= (/) -> E. f ( f : A --> U. A /\ A. x e. A ( f ` x ) e. x ) )

  proof
    vx
    cv
    #
    c0
    wne
    #
    vx
    cA
    wral
    #
    cA
    cuni
    #
    ccrd
    cdm
    wcel
    #
    c0
    cA
    wcel
    #
    wn
    cA
    @3
    vf
    cv
    #
    wf
    @0
    @6
    cfv
    @0
    wcel
    vx
    cA
    wral
    wa
    vf
    wex
    @3
    cvv
    wcel
    @4
    @2
    cA
    ac5b.1
    uniex
    @3
    cvv
    numth3
    mp1i
    @2
    @5
    c0
    c0
    wne
    #
    c0
    neirr
    @1
    @7
    vx
    c0
    cA
    @0
    c0
    c0
    neeq1
    rspccv
    mtoi
    vx
    cA
    vf
    ac5num
    syl2anc
end
