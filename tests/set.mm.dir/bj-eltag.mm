include "bj-ctag.mm"
include "wcel.mm"
include "bj-csngl.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wo.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "df-bj-tag.mm"
include "eleq2i.mm"
include "elun.mm"
include "bj-elsngl.mm"
include "0ex.mm"
include "elsn2.mm"
include "orbi12i.mm"
include "3bitri.mm"

theorem bj-eltag
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A e. tag B <-> ( E. x e. B A = { x } \/ A = (/) ) )

  proof
    cA
    cB
    bj-ctag
    #
    wcel
    cA
    cB
    bj-csngl
    #
    c0
    csn
    #
    cun
    #
    wcel
    cA
    @1
    wcel
    #
    cA
    @2
    wcel
    #
    wo
    cA
    vx
    cv
    csn
    wceq
    vx
    cB
    wrex
    #
    cA
    c0
    wceq
    #
    wo
    @0
    @3
    cA
    cB
    df-bj-tag
    eleq2i
    cA
    @1
    @2
    elun
    @4
    @6
    @5
    @7
    vx
    cA
    cB
    bj-elsngl
    cA
    c0
    0ex
    elsn2
    orbi12i
    3bitri
end
