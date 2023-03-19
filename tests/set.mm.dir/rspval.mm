include "crsp.mm"
include "cfv.mm"
include "clspn.mm"
include "crglmod.mm"
include "ccom.mm"
include "df-rsp.mm"
include "fveq1i.mm"
include "00lsp.mm"
include "cvv.mm"
include "wfn.mm"
include "wfun.mm"
include "rlmfn.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fvco4i.mm"
include "eqtri.mm"

theorem rspval
  let cW: class W
  let va: setvar a


  assert |- ( RSpan ` W ) = ( LSpan ` ( ringLMod ` W ) )

  proof
    cW
    crsp
    cfv
    cW
    clspn
    crglmod
    ccom
    #
    cfv
    cW
    crglmod
    cfv
    clspn
    cfv
    cW
    crsp
    @0
    df-rsp
    fveq1i
    clspn
    crglmod
    cW
    00lsp
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
