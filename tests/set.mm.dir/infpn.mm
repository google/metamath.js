include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "eqid.mm"
include "infpnlem2.mm"

theorem infpn
  let vj: setvar j
  let vk: setvar k
  let cN: class N

  disjoint j k
  disjoint N j
  disjoint N k
  assert |- ( N e. NN -> E. j e. NN ( N < j /\ A. k e. NN ( ( j / k ) e. NN -> ( k = 1 \/ k = j ) ) ) )

  proof
    vj
    vk
    cN
    cfa
    cfv
    c1
    caddc
    co
    #
    cN
    @0
    eqid
    infpnlem2
end
