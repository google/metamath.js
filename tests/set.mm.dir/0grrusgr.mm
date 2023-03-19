include "c0.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "cv.mm"
include "crusgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "wral.mm"
include "0ex.mm"
include "vtxval0.mm"
include "iedgval0.mm"
include "0vtxrusgr.mm"
include "mp3an.mm"

theorem 0grrusgr
  let vk: setvar k
  let cG: class G
  let vv: setvar v
  let cW: class W


  assert |- A. k e. NN0* (/) RegUSGraph k

  proof
    c0
    cvv
    wcel
    c0
    cvtx
    cfv
    c0
    wceq
    c0
    ciedg
    cfv
    c0
    wceq
    c0
    vk
    cv
    crusgr
    wbr
    vk
    cxnn0
    wral
    0ex
    vtxval0
    iedgval0
    vk
    c0
    cvv
    0vtxrusgr
    mp3an
end
