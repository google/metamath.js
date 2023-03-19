include "cin.mm"
include "wss.mm"
include "wfun.mm"
include "wi.mm"
include "inss1.mm"
include "funss.mm"
include "ax-mp.mm"

theorem funin
  let cF: class F
  let cG: class G


  assert |- ( Fun F -> Fun ( F i^i G ) )

  proof
    cF
    cG
    cin
    #
    cF
    wss
    cF
    wfun
    @0
    wfun
    wi
    cF
    cG
    inss1
    @0
    cF
    funss
    ax-mp
end
