include "ccusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "iscusgr.mm"
include "simplbi.mm"

theorem cusgrusgr
  let cG: class G


  assert |- ( G e. ComplUSGraph -> G e. USGraph )

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
    simplbi
end
