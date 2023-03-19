include "cafv.mm"
include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "wi.mm"
include "0ex.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "afvvfveq.mm"
include "eqeq1.mm"
include "biimpd.mm"
include "syl.mm"
include "mpcom.mm"

theorem afv0fv0
  let cA: class A
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ''' A ) = (/) -> ( F ` A ) = (/) )

  proof
    cA
    cF
    cafv
    #
    cvv
    wcel
    #
    @0
    c0
    wceq
    #
    cA
    cF
    cfv
    #
    c0
    wceq
    #
    c0
    cvv
    wcel
    @2
    @1
    wi
    0ex
    c0
    cvv
    @0
    eleq1a
    ax-mp
    @1
    @0
    @3
    wceq
    #
    @2
    @4
    wi
    cA
    cvv
    cF
    afvvfveq
    @5
    @2
    @4
    @0
    @3
    c0
    eqeq1
    biimpd
    syl
    mpcom
end
