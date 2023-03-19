include "ccnv.mm"
include "wss.mm"
include "wfun.mm"
include "wi.mm"
include "cnvcnvss.mm"
include "funss.mm"
include "ax-mp.mm"

theorem funcnvcnv
  let cA: class A


  assert |- ( Fun A -> Fun `' `' A )

  proof
    cA
    ccnv
    ccnv
    #
    cA
    wss
    cA
    wfun
    @0
    wfun
    wi
    cA
    cnvcnvss
    @0
    cA
    funss
    ax-mp
end
