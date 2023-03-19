include "cusgr.mm"
include "ccplgr.mm"
include "ccusgr.mm"
include "df-cusgr.mm"
include "elin2.mm"

theorem iscusgr
  let cG: class G


  assert |- ( G e. ComplUSGraph <-> ( G e. USGraph /\ G e. ComplGraph ) )

  proof
    cG
    cusgr
    ccplgr
    ccusgr
    df-cusgr
    elin2
end
