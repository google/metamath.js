include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "wn.mm"
include "cat.mm"
include "wral.mm"
include "wi.mm"
include "wrex.mm"
include "chrelat2.mm"
include "dfrex2.mm"
include "syl6bb.mm"
include "con4bid.mm"
include "iman.mm"
include "ralbii.mm"
include "syl6bbr.mm"

theorem chrelat3
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_ B <-> A. x e. HAtoms ( x C_ A -> x C_ B ) ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    wa
    #
    cA
    cB
    wss
    #
    vx
    cv
    #
    cA
    wss
    #
    @2
    cB
    wss
    #
    wn
    wa
    #
    wn
    #
    vx
    cat
    wral
    #
    @3
    @4
    wi
    #
    vx
    cat
    wral
    @0
    @1
    @7
    @0
    @1
    wn
    @5
    vx
    cat
    wrex
    @7
    wn
    vx
    cA
    cB
    chrelat2
    @5
    vx
    cat
    dfrex2
    syl6bb
    con4bid
    @8
    @6
    vx
    cat
    @3
    @4
    iman
    ralbii
    syl6bbr
end
