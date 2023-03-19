include "cxnn0.mm"
include "wcel.mm"
include "cn0.mm"
include "wn.mm"
include "cpnf.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "elxnn0.mm"
include "pm2.53.mm"
include "sylbi.mm"
include "imp.mm"

theorem xnn0nnn0pnf
  let cN: class N


  assert |- ( ( N e. NN0* /\ -. N e. NN0 ) -> N = +oo )

  proof
    cN
    cxnn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wn
    #
    cN
    cpnf
    wceq
    #
    @0
    @1
    @3
    wo
    @2
    @3
    wi
    cN
    elxnn0
    @1
    @3
    pm2.53
    sylbi
    imp
end
