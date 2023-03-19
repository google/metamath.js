include "c0.mm"
include "cconngr.mm"
include "wcel.mm"
include "cv.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "wral.mm"
include "ral0.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "cvtx.mm"
include "vtxval0.mm"
include "eqcomi.mm"
include "isconngr.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem 0conngr
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p


  assert |- (/) e. ConnGraph

  proof
    c0
    cconngr
    wcel
    #
    vf
    cv
    vp
    cv
    vk
    cv
    vn
    cv
    c0
    cpthson
    cfv
    co
    wbr
    vp
    wex
    vf
    wex
    vn
    c0
    wral
    #
    vk
    c0
    wral
    #
    @1
    vk
    ral0
    c0
    cvv
    wcel
    @0
    @2
    wb
    0ex
    vf
    vk
    vn
    c0
    c0
    cvv
    vp
    c0
    cvtx
    cfv
    c0
    vtxval0
    eqcomi
    isconngr
    ax-mp
    mpbir
end
