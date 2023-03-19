include "c3.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c5.mm"
include "cdc.mm"
include "c7.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "3nn0.mm"
include "fmtno.mm"
include "ax-mp.mm"
include "c8.mm"
include "c6.mm"
include "cu2.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "2exp8.mm"
include "2nn0.mm"
include "5nn0.mm"
include "deccl.mm"
include "6nn0.mm"
include "6p1e7.mm"
include "eqid.mm"
include "decsuc.mm"
include "3eqtri.mm"
include "eqtri.mm"

theorem fmtno3
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 3 ) = ; ; 2 5 7

  proof
    c3
    cfmtno
    cfv
    #
    c2
    c2
    c3
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
    c2
    c5
    cdc
    #
    c7
    cdc
    #
    c3
    cn0
    wcel
    @0
    @3
    wceq
    3nn0
    c3
    fmtno
    ax-mp
    @3
    c2
    c8
    cexp
    co
    #
    c1
    caddc
    co
    @4
    c6
    cdc
    #
    c1
    caddc
    co
    @5
    @2
    @6
    c1
    caddc
    @1
    c8
    c2
    cexp
    cu2
    oveq2i
    oveq1i
    @6
    @7
    c1
    caddc
    2exp8
    oveq1i
    @4
    c6
    c7
    @7
    c2
    c5
    2nn0
    5nn0
    deccl
    6nn0
    6p1e7
    @7
    eqid
    decsuc
    3eqtri
    eqtri
end
