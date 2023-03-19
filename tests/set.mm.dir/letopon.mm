include "cle.mm"
include "ctsr.mm"
include "wcel.mm"
include "cordt.mm"
include "cfv.mm"
include "cxr.mm"
include "ctopon.mm"
include "letsr.mm"
include "ledm.mm"
include "ordttopon.mm"
include "ax-mp.mm"

theorem letopon



  assert |- ( ordTop ` <_ ) e. ( TopOn ` RR* )

  proof
    cle
    ctsr
    wcel
    cle
    cordt
    cfv
    cxr
    ctopon
    cfv
    wcel
    letsr
    cle
    ctsr
    cxr
    ledm
    ordttopon
    ax-mp
end
