include "ccusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "iscusgr.mm"
include "simprbi.mm"

theorem cusgrcplgr
  let cG: class G


  assert |- ( G e. ComplUSGraph -> G e. ComplGraph )

  proof
    cG
    ccusgr
    wcel
    cG
    cusgr
    wcel
    cG
    ccplgr
    wcel
    cG
    iscusgr
    simprbi
end
