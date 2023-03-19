include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cvv.mm"
include "cv.mm"
include "csn.mm"
include "cuni.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "simpr.mm"
include "cnvexg.mm"
include "adantl.mm"
include "cnvf1o.mm"
include "adantr.mm"
include "f1oen2g.mm"
include "syl3anc.mm"

theorem cnven
  let cA: class A
  let cV: class V
  let vx: setvar x
  let cF: class F


  assert |- ( ( Rel A /\ A e. V ) -> A ~~ `' A )

  proof
    cA
    wrel
    #
    cA
    cV
    wcel
    #
    wa
    @1
    cA
    ccnv
    #
    cvv
    wcel
    #
    cA
    @2
    vx
    cA
    vx
    cv
    csn
    ccnv
    cuni
    cmpt
    #
    wf1o
    #
    cA
    @2
    cen
    wbr
    @0
    @1
    simpr
    @1
    @3
    @0
    cA
    cV
    cnvexg
    adantl
    @0
    @5
    @1
    vx
    cA
    cnvf1o
    adantr
    cA
    @2
    @4
    cV
    cvv
    f1oen2g
    syl3anc
end
