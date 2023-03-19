include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "uniexr.mm"
include "adantl.mm"
include "bj-restb.mm"
include "mpcom.mm"

theorem bj-restv
  let cA: class A
  let cX: class X


  assert |- ( ( A C_ U. X /\ U. X e. X ) -> A e. ( X |`t A ) )

  proof
    cX
    cvv
    wcel
    #
    cA
    cX
    cuni
    #
    wss
    #
    @1
    cX
    wcel
    #
    wa
    cA
    cX
    cA
    crest
    co
    wcel
    @3
    @0
    @2
    cX
    cX
    uniexr
    adantl
    cA
    @1
    cvv
    cX
    bj-restb
    mpcom
end
