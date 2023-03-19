include "cres.mm"
include "wss.mm"
include "wfun.mm"
include "wi.mm"
include "resss.mm"
include "funss.mm"
include "ax-mp.mm"

theorem funres
  let cA: class A
  let cF: class F


  assert |- ( Fun F -> Fun ( F |` A ) )

  proof
    cF
    cA
    cres
    #
    cF
    wss
    cF
    wfun
    @0
    wfun
    wi
    cF
    cA
    resss
    @0
    cF
    funss
    ax-mp
end
