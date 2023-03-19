include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cvv.mm"
include "wrdf.mm"
include "wss.mm"
include "ssv.mm"
include "fss.mm"
include "mpan2.mm"
include "iswrdi.mm"
include "3syl.mm"

theorem wrdv
  let cV: class V
  let cW: class W


  assert |- ( W e. Word V -> W e. Word _V )

  proof
    cW
    cV
    cword
    wcel
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cV
    cW
    wf
    #
    @1
    cvv
    cW
    wf
    #
    cW
    cvv
    cword
    wcel
    cV
    cW
    wrdf
    @2
    cV
    cvv
    wss
    @3
    cV
    ssv
    @1
    cV
    cvv
    cW
    fss
    mpan2
    cvv
    @0
    cW
    iswrdi
    3syl
end
