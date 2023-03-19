include "c5.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cprime.mm"
include "c6.mm"
include "c7.mm"
include "cdc.mm"
include "cc0.mm"
include "c4.mm"
include "c1.mm"
include "6nn0.mm"
include "7nn0.mm"
include "deccl.mm"
include "0nn0.mm"
include "4nn0.mm"
include "1nn0.mm"
include "7nn.mm"
include "decnncl.mm"
include "1nn.mm"
include "1lt10.mm"
include "declti.mm"
include "4nn.mm"
include "cmul.mm"
include "co.mm"
include "fmtno5fac.mm"
include "eqcomi.mm"
include "nprmi.mm"
include "nelir.mm"

theorem fmtno5nprm
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 5 ) e/ Prime

  proof
    c5
    cfmtno
    cfv
    #
    cprime
    c6
    c7
    cdc
    #
    cc0
    cdc
    #
    cc0
    cdc
    #
    c4
    cdc
    #
    c1
    cdc
    #
    c7
    cdc
    #
    c6
    c4
    cdc
    #
    c1
    cdc
    #
    @0
    @5
    c7
    @4
    c1
    @3
    c4
    @2
    cc0
    @1
    cc0
    c6
    c7
    6nn0
    7nn0
    deccl
    0nn0
    deccl
    0nn0
    deccl
    4nn0
    deccl
    #
    1nn0
    deccl
    7nn
    decnncl
    @7
    c1
    c6
    c4
    6nn0
    4nn0
    deccl
    1nn
    decnncl
    @5
    c7
    c1
    @4
    c1
    @9
    1nn
    decnncl
    7nn0
    1nn0
    1lt10
    declti
    @7
    c1
    c1
    c6
    c4
    6nn0
    4nn
    decnncl
    1nn0
    1nn0
    1lt10
    declti
    @0
    @6
    @8
    cmul
    co
    fmtno5fac
    eqcomi
    nprmi
    nelir
end
