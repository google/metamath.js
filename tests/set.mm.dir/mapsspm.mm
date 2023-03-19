include "cmap.mm"
include "co.mm"
include "cpm.mm"
include "cv.mm"
include "wcel.mm"
include "cvv.mm"
include "wf.mm"
include "elmapex.mm"
include "simprd.mm"
include "simpld.mm"
include "elmapi.mm"
include "fpmg.mm"
include "syl3anc.mm"
include "ssriv.mm"

theorem mapsspm
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( A ^m B ) C_ ( A ^pm B )

  proof
    vf
    cA
    cB
    cmap
    co
    #
    cA
    cB
    cpm
    co
    #
    vf
    cv
    #
    @0
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cA
    @2
    wf
    @2
    @1
    wcel
    @3
    @5
    @4
    @2
    cA
    cB
    elmapex
    #
    simprd
    @3
    @5
    @4
    @6
    simpld
    @2
    cA
    cB
    elmapi
    cB
    cA
    @2
    cvv
    cvv
    fpmg
    syl3anc
    ssriv
end
