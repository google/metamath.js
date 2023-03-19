include "c0.mm"
include "ccusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "ccplgr.mm"
include "usgr0.mm"
include "cplgr0.mm"
include "iscusgr.mm"
include "mpbir2an.mm"

theorem cusgr0



  assert |- (/) e. ComplUSGraph

  proof
    c0
    ccusgr
    wcel
    c0
    cusgr
    wcel
    c0
    ccplgr
    wcel
    usgr0
    cplgr0
    c0
    iscusgr
    mpbir2an
end
