include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "zfreg.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylib.mm"
include "wb.mm"
include "simpl.mm"
include "elrest.mm"
include "syldan.mm"
include "mpbird.mm"

theorem bj-restreg
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( ( A e. V /\ A =/= (/) ) -> (/) e. ( A |`t A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    wne
    #
    wa
    #
    c0
    cA
    cA
    crest
    co
    wcel
    #
    c0
    vx
    cv
    cA
    cin
    #
    wceq
    #
    vx
    cA
    wrex
    #
    @2
    @4
    c0
    wceq
    #
    vx
    cA
    wrex
    @6
    vx
    cA
    cV
    zfreg
    @7
    @5
    vx
    cA
    @4
    c0
    eqcom
    rexbii
    sylib
    @0
    @1
    @0
    @3
    @6
    wb
    @0
    @1
    simpl
    vx
    c0
    cA
    cA
    cV
    cV
    elrest
    syldan
    mpbird
end
