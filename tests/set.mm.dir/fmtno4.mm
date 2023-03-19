include "c4.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c6.mm"
include "c5.mm"
include "cdc.mm"
include "c3.mm"
include "c7.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "4nn0.mm"
include "fmtno.mm"
include "ax-mp.mm"
include "2exp4.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "2exp16.mm"
include "6nn0.mm"
include "5nn0.mm"
include "deccl.mm"
include "3nn0.mm"
include "6p1e7.mm"
include "eqid.mm"
include "decsuc.mm"
include "3eqtri.mm"
include "eqtri.mm"

theorem fmtno4
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 4 ) = ; ; ; ; 6 5 5 3 7

  proof
    c4
    cfmtno
    cfv
    #
    c2
    c2
    c4
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    c6
    c5
    cdc
    #
    c5
    cdc
    #
    c3
    cdc
    #
    c7
    cdc
    #
    c4
    cn0
    wcel
    @0
    @3
    wceq
    4nn0
    c4
    fmtno
    ax-mp
    @3
    c2
    c1
    c6
    cdc
    #
    cexp
    co
    #
    c1
    caddc
    co
    @6
    c6
    cdc
    #
    c1
    caddc
    co
    @7
    @2
    @9
    c1
    caddc
    @1
    @8
    c2
    cexp
    2exp4
    oveq2i
    oveq1i
    @9
    @10
    c1
    caddc
    2exp16
    oveq1i
    @6
    c6
    c7
    @10
    @5
    c3
    @4
    c5
    c6
    c5
    6nn0
    5nn0
    deccl
    5nn0
    deccl
    3nn0
    deccl
    6nn0
    6p1e7
    @10
    eqid
    decsuc
    3eqtri
    eqtri
end
