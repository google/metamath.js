include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cxr.mm"
include "ctopon.mm"
include "wcel.mm"
include "cxrs.mm"
include "ctps.mm"
include "letopon.mm"
include "xrsbas.mm"
include "xrstset.mm"
include "tsettps.mm"
include "ax-mp.mm"

theorem xrstps



  assert |- RR*s e. TopSp

  proof
    cle
    cordt
    cfv
    #
    cxr
    ctopon
    cfv
    wcel
    cxrs
    ctps
    wcel
    letopon
    cxr
    @0
    cxrs
    xrsbas
    xrstset
    tsettps
    ax-mp
end
