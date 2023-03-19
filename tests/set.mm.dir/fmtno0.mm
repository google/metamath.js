include "cc0.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "c3.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "0nn0.mm"
include "fmtno.mm"
include "ax-mp.mm"
include "cc.mm"
include "2cn.mm"
include "exp0.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "exp1.mm"
include "2p1e3.mm"
include "3eqtri.mm"
include "eqtri.mm"

theorem fmtno0
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 0 ) = 3

  proof
    cc0
    cfmtno
    cfv
    #
    c2
    c2
    cc0
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
    c3
    cc0
    cn0
    wcel
    @0
    @3
    wceq
    0nn0
    cc0
    fmtno
    ax-mp
    @3
    c2
    c1
    cexp
    co
    #
    c1
    caddc
    co
    c2
    c1
    caddc
    co
    c3
    @2
    @4
    c1
    caddc
    @1
    c1
    c2
    cexp
    c2
    cc
    wcel
    #
    @1
    c1
    wceq
    2cn
    c2
    exp0
    ax-mp
    oveq2i
    oveq1i
    @4
    c2
    c1
    caddc
    @5
    @4
    c2
    wceq
    2cn
    c2
    exp1
    ax-mp
    oveq1i
    2p1e3
    3eqtri
    eqtri
end
