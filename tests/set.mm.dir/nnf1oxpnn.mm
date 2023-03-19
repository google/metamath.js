include "cn.mm"
include "cxp.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "xpnnen.mm"
include "ensymi.mm"
include "bren.mm"
include "mpbi.mm"

theorem nnf1oxpnn
  let vf: setvar f


  assert |- E. f f : NN -1-1-onto-> ( NN X. NN )

  proof
    cn
    cn
    cn
    cxp
    #
    cen
    wbr
    cn
    @0
    vf
    cv
    wf1o
    vf
    wex
    @0
    cn
    xpnnen
    ensymi
    cn
    @0
    vf
    bren
    mpbi
end
