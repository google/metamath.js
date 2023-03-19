include "cumgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "cuhgr.mm"
include "umgrupgr.mm"
include "upgruhgr.mm"
include "syl.mm"

theorem umgruhgr
  let cG: class G


  assert |- ( G e. UMGraph -> G e. UHGraph )

  proof
    cG
    cumgr
    wcel
    cG
    cupgr
    wcel
    cG
    cuhgr
    wcel
    cG
    umgrupgr
    cG
    upgruhgr
    syl
end
