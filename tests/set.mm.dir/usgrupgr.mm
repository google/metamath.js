include "cusgr.mm"
include "wcel.mm"
include "cuspgr.mm"
include "cupgr.mm"
include "usgruspgr.mm"
include "uspgrupgr.mm"
include "syl.mm"

theorem usgrupgr
  let cG: class G


  assert |- ( G e. USGraph -> G e. UPGraph )

  proof
    cG
    cusgr
    wcel
    cG
    cuspgr
    wcel
    cG
    cupgr
    wcel
    cG
    usgruspgr
    cG
    uspgrupgr
    syl
end
