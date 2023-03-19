include "wcel.mm"
include "wral.mm"
include "cixp.mm"
include "ciun.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wa.mm"
include "cvv.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "ixpprc.mm"
include "nsyl2.mm"
include "id.mm"
include "iunexg.mm"
include "syl2anr.mm"
include "ixpssmap2g.mm"
include "syl.mm"
include "simpr.mm"
include "sseldd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem ixpssmapg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f

  disjoint A x
  disjoint A f
  disjoint f x
  disjoint B f
  disjoint V f
  assert |- ( A. x e. A B e. V -> X_ x e. A B C_ ( U_ x e. A B ^m A ) )

  proof
    cB
    cV
    wcel
    vx
    cA
    wral
    #
    vf
    vx
    cA
    cB
    cixp
    #
    vx
    cA
    cB
    ciun
    #
    cA
    cmap
    co
    #
    @0
    vf
    cv
    #
    @1
    wcel
    #
    @4
    @3
    wcel
    @0
    @5
    wa
    #
    @1
    @3
    @4
    @6
    @2
    cvv
    wcel
    #
    @1
    @3
    wss
    @5
    cA
    cvv
    wcel
    #
    @0
    @7
    @0
    @5
    @1
    c0
    wceq
    @8
    @1
    @4
    n0i
    vx
    cA
    cB
    ixpprc
    nsyl2
    @0
    id
    vx
    cA
    cB
    cvv
    cV
    iunexg
    syl2anr
    vx
    cA
    cB
    cvv
    ixpssmap2g
    syl
    @0
    @5
    simpr
    sseldd
    ex
    ssrdv
end
