include "clidl.mm"
include "cfv.mm"
include "clss.mm"
include "crglmod.mm"
include "ccom.mm"
include "df-lidl.mm"
include "fveq1i.mm"
include "00lss.mm"
include "cvv.mm"
include "wfn.mm"
include "wfun.mm"
include "rlmfn.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvco4i.mm"
include "eqtri.mm"

theorem lidlval
  let cW: class W
  let va: setvar a


  assert |- ( LIdeal ` W ) = ( LSubSp ` ( ringLMod ` W ) )

  proof
    cW
    clidl
    cfv
    cW
    clss
    crglmod
    ccom
    #
    cfv
    cW
    crglmod
    cfv
    clss
    cfv
    cW
    clidl
    @0
    df-lidl
    fveq1i
    clss
    crglmod
    cW
    00lss
    crglmod
    cvv
    wfn
    crglmod
    wfun
    rlmfn
    cvv
    crglmod
    fnfun
    ax-mp
    fvco4i
    eqtri
end
