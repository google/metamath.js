include "cfunpart.mm"
include "cimage.mm"
include "csingle.mm"
include "ccom.mm"
include "cvv.mm"
include "csingles.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "cres.mm"
include "df-funpart.mm"
include "resss.mm"
include "eqsstri.mm"

theorem funpartss
  let cF: class F


  assert |- Funpart F C_ F

  proof
    cF
    cfunpart
    cF
    cF
    cimage
    csingle
    ccom
    cvv
    csingles
    cxp
    cin
    cdm
    #
    cres
    cF
    cF
    df-funpart
    cF
    @0
    resss
    eqsstri
end
