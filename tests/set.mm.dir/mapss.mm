include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "simplr.mm"
include "fssd.mm"
include "cvv.mm"
include "simpll.mm"
include "elmapex.mm"
include "simprd.mm"
include "elmapd.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"

theorem mapss
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vf: setvar f


  assert |- ( ( B e. V /\ A C_ B ) -> ( A ^m C ) C_ ( B ^m C ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    vf
    cA
    cC
    cmap
    co
    #
    cB
    cC
    cmap
    co
    #
    @2
    vf
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    @7
    cC
    cB
    @5
    wf
    @8
    cC
    cA
    cB
    @5
    @6
    cC
    cA
    @5
    wf
    @2
    @5
    cA
    cC
    elmapi
    adantl
    @0
    @1
    @6
    simplr
    fssd
    @8
    cB
    cC
    @5
    cV
    cvv
    @0
    @1
    @6
    simpll
    @6
    cC
    cvv
    wcel
    #
    @2
    @6
    cA
    cvv
    wcel
    @9
    @5
    cA
    cC
    elmapex
    simprd
    adantl
    elmapd
    mpbird
    ex
    ssrdv
end
