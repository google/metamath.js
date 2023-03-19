include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cdv.mm"
include "co.mm"
include "cdm.mm"
include "wf.mm"
include "reelprrecn.mm"
include "dvfg.mm"
include "ax-mp.mm"

theorem dvf
  let cF: class F


  assert |- ( RR _D F ) : dom ( RR _D F ) --> CC

  proof
    cr
    cr
    cc
    cpr
    wcel
    cr
    cF
    cdv
    co
    #
    cdm
    cc
    @0
    wf
    reelprrecn
    cr
    cF
    dvfg
    ax-mp
end
