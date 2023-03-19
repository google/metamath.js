include "cid.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "id.mm"
include "cvv.mm"
include "wceq.mm"
include "elfvex.mm"
include "fvi.mm"
include "syl.mm"
include "eleqtrd.mm"
include "ssriv.mm"

theorem fviss
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F


  assert |- ( _I ` A ) C_ A

  proof
    vx
    cA
    cid
    cfv
    #
    cA
    vx
    cv
    #
    @0
    wcel
    #
    @1
    @0
    cA
    @2
    id
    @2
    cA
    cvv
    wcel
    @0
    cA
    wceq
    @1
    cA
    cid
    elfvex
    cA
    cvv
    fvi
    syl
    eleqtrd
    ssriv
end
