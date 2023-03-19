include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "carden.mm"
include "mpan2.mm"
include "card0.mm"
include "eqeq2i.mm"
include "en0.mm"
include "3bitr3g.mm"

theorem cardeq0
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( ( card ` A ) = (/) <-> A = (/) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    ccrd
    cfv
    #
    c0
    ccrd
    cfv
    #
    wceq
    #
    cA
    c0
    cen
    wbr
    #
    @1
    c0
    wceq
    cA
    c0
    wceq
    @0
    c0
    cvv
    wcel
    @3
    @4
    wb
    0ex
    cA
    c0
    cV
    cvv
    carden
    mpan2
    @2
    c0
    @1
    card0
    eqeq2i
    cA
    en0
    3bitr3g
end
