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
include "andi.mm"
include "df-3or.mm"
include "anbi2i.mm"
include "nn0re.mm"
include "pm4.71ri.mm"
include "elnn0.mm"
include "orcom.mm"
include "bitri.mm"
include "orbi1i.mm"
include "3bitr4i.mm"

theorem elznn0nn
  let cN: class N


  assert |- ( N e. ZZ <-> ( N e. NN0 \/ ( N e. RR /\ -u N e. NN ) ) )

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
    cn
    wcel
    #
    w3o
    #
    wa
    #
    cN
    cn0
    wcel
    #
    @0
    @3
    wa
    #
    wo
    #
    cN
    elz
    @0
    @1
    @2
    wo
    #
    @3
    wo
    #
    wa
    @0
    @9
    wa
    #
    @7
    wo
    @5
    @8
    @0
    @9
    @3
    andi
    @4
    @10
    @0
    @1
    @2
    @3
    df-3or
    anbi2i
    @6
    @11
    @7
    @6
    @0
    @6
    wa
    @11
    @6
    @0
    cN
    nn0re
    pm4.71ri
    @6
    @9
    @0
    @6
    @2
    @1
    wo
    @9
    cN
    elnn0
    @2
    @1
    orcom
    bitri
    anbi2i
    bitri
    orbi1i
    3bitr4i
    bitri
end
