include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "ctp.mm"
include "elisset.mm"
include "w3o.mm"
include "cab.mm"
include "wi.mm"
include "3mix3.mm"
include "a1i.mm"
include "abid.mm"
include "syl6ibr.mm"
include "dftp2.mm"
include "eleq2i.mm"
include "eleq1.mm"
include "mpbidi.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem tpid3gOLD
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( A e. B -> A e. { C , D , A } )

  proof
    cA
    cB
    wcel
    #
    vx
    cv
    #
    cA
    wceq
    #
    vx
    wex
    cA
    cC
    cD
    cA
    ctp
    #
    wcel
    #
    vx
    cA
    cB
    elisset
    @0
    @2
    @4
    vx
    @2
    @1
    @3
    wcel
    #
    @4
    @0
    @0
    @2
    @1
    @1
    cC
    wceq
    #
    @1
    cD
    wceq
    #
    @2
    w3o
    #
    vx
    cab
    #
    wcel
    #
    @5
    @0
    @2
    @8
    @10
    @2
    @8
    wi
    @0
    @2
    @6
    @7
    3mix3
    a1i
    @8
    vx
    abid
    syl6ibr
    @3
    @9
    @1
    vx
    cC
    cD
    cA
    dftp2
    eleq2i
    syl6ibr
    @1
    cA
    @3
    eleq1
    mpbidi
    exlimdv
    mpd
end
