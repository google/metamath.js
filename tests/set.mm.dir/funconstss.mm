include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cima.mm"
include "csn.mm"
include "ccnv.mm"
include "wcel.mm"
include "funimass4.mm"
include "fvex.mm"
include "elsn.mm"
include "ralbii.mm"
include "syl6rbb.mm"
include "funimass3.mm"
include "bitrd.mm"

theorem funconstss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint F x
  disjoint A x
  disjoint B x
  assert |- ( ( Fun F /\ A C_ dom F ) -> ( A. x e. A ( F ` x ) = B <-> A C_ ( `' F " { B } ) ) )

  proof
    cF
    wfun
    cA
    cF
    cdm
    wss
    wa
    #
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wceq
    #
    vx
    cA
    wral
    #
    cF
    cA
    cima
    cB
    csn
    #
    wss
    #
    cA
    cF
    ccnv
    @5
    cima
    wss
    @0
    @6
    @2
    @5
    wcel
    #
    vx
    cA
    wral
    @4
    vx
    cA
    @5
    cF
    funimass4
    @7
    @3
    vx
    cA
    @2
    cB
    @1
    cF
    fvex
    elsn
    ralbii
    syl6rbb
    cA
    @5
    cF
    funimass3
    bitrd
end
