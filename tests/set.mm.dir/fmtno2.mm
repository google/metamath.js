include "c2.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c7.mm"
include "cdc.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "2nn0.mm"
include "fmtno.mm"
include "ax-mp.mm"
include "c4.mm"
include "c6.mm"
include "sq2.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "2exp4.mm"
include "1nn0.mm"
include "6nn0.mm"
include "6p1e7.mm"
include "eqid.mm"
include "decsuc.mm"
include "3eqtri.mm"
include "eqtri.mm"

theorem fmtno2
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 2 ) = ; 1 7

  proof
    c2
    cfmtno
    cfv
    #
    c2
    c2
    c2
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
    c1
    c7
    cdc
    #
    c2
    cn0
    wcel
    @0
    @3
    wceq
    2nn0
    c2
    fmtno
    ax-mp
    @3
    c2
    c4
    cexp
    co
    #
    c1
    caddc
    co
    c1
    c6
    cdc
    #
    c1
    caddc
    co
    @4
    @2
    @5
    c1
    caddc
    @1
    c4
    c2
    cexp
    sq2
    oveq2i
    oveq1i
    @5
    @6
    c1
    caddc
    2exp4
    oveq1i
    c1
    c6
    c7
    @6
    1nn0
    6nn0
    6p1e7
    @6
    eqid
    decsuc
    3eqtri
    eqtri
end
