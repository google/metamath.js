include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "cneg.mm"
include "w3o.mm"
include "wa.mm"
include "cn0.mm"
include "wo.mm"
include "elz.mm"
include "recn.mm"
include "negeq0d.mm"
include "orbi2d.mm"
include "elnn0.mm"
include "syl6rbbr.mm"
include "3orrot.mm"
include "3orass.mm"
include "bitri.mm"
include "pm5.32i.mm"

theorem elznn
  let cN: class N


  assert |- ( N e. ZZ <-> ( N e. RR /\ ( N e. NN \/ -u N e. NN0 ) ) )

  proof
    cN
    cz
    wcel
    cN
    cr
    wcel
    #
    cN
    cc0
    wceq
    #
    cN
    cn
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    w3o
    #
    wa
    @0
    @2
    @3
    cn0
    wcel
    #
    wo
    #
    wa
    cN
    elz
    @0
    @5
    @7
    @0
    @7
    @2
    @4
    @1
    wo
    #
    wo
    #
    @5
    @0
    @6
    @8
    @2
    @0
    @8
    @4
    @3
    cc0
    wceq
    #
    wo
    @6
    @0
    @1
    @10
    @4
    @0
    cN
    cN
    recn
    negeq0d
    orbi2d
    @3
    elnn0
    syl6rbbr
    orbi2d
    @5
    @2
    @4
    @1
    w3o
    @9
    @1
    @2
    @4
    3orrot
    @2
    @4
    @1
    3orass
    bitri
    syl6rbbr
    pm5.32i
    bitri
end
