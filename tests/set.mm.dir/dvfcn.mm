include "cc.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wf.mm"
include "cnelprrecn.mm"
include "dvfg.mm"
include "ax-mp.mm"

theorem dvfcn
  let cF: class F


  assert |- ( CC _D F ) : dom ( CC _D F ) --> CC

  proof
    cc
    cr
    cc
    cpr
    wcel
    cc
    cF
    cdv
    co
    #
    cdm
    cc
    @0
    wf
    cnelprrecn
    cc
    cF
    dvfg
    ax-mp
end
