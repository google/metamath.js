include "cvv.mm"
include "cbigcup.mm"
include "wfo.mm"
include "wfn.mm"
include "fobigcup.mm"
include "fofn.mm"
include "ax-mp.mm"

theorem fnbigcup



  assert |- Bigcup Fn _V

  proof
    cvv
    cvv
    cbigcup
    wfo
    cbigcup
    cvv
    wfn
    fobigcup
    cvv
    cvv
    cbigcup
    fofn
    ax-mp
end
