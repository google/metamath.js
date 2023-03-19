include "cpnf.mm"
include "cpw.mm"
include "cmnf.mm"
include "cxr.mm"
include "wcel.mm"
include "wne.mm"
include "pnfxr.mm"
include "pwne.mm"
include "ax-mp.mm"
include "necomi.mm"
include "df-mnf.mm"
include "neeqtrri.mm"

theorem pnfnemnf



  assert |- +oo =/= -oo

  proof
    cpnf
    cpnf
    cpw
    #
    cmnf
    @0
    cpnf
    cpnf
    cxr
    wcel
    @0
    cpnf
    wne
    pnfxr
    cpnf
    cxr
    pwne
    ax-mp
    necomi
    df-mnf
    neeqtrri
end
