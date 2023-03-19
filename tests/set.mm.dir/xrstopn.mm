include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "cxr.mm"
include "ctopon.mm"
include "wcel.mm"
include "cxrs.mm"
include "ctopn.mm"
include "wceq.mm"
include "letopon.mm"
include "xrsbas.mm"
include "xrstset.mm"
include "topontopn.mm"
include "ax-mp.mm"

theorem xrstopn



  assert |- ( ordTop ` <_ ) = ( TopOpen ` RR*s )

  proof
    cle
    cordt
    cfv
    #
    cxr
    ctopon
    cfv
    wcel
    @0
    cxrs
    ctopn
    cfv
    wceq
    letopon
    cxr
    @0
    cxrs
    xrsbas
    xrstset
    topontopn
    ax-mp
end
