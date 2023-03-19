include "cusgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "cuhgr.mm"
include "usgrupgr.mm"
include "upgruhgr.mm"
include "syl.mm"

theorem usgruhgr
  let cG: class G


  assert |- ( G e. USGraph -> G e. UHGraph )

  proof
    cG
    cusgr
    wcel
    cG
    cupgr
    wcel
    cG
    cuhgr
    wcel
    cG
    usgrupgr
    cG
    upgruhgr
    syl
end
