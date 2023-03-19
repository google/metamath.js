include "c1.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "c5.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "1nn0.mm"
include "fmtno.mm"
include "ax-mp.mm"
include "c4.mm"
include "cc.mm"
include "2cn.mm"
include "exp1.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "sq2.mm"
include "4p1e5.mm"
include "3eqtri.mm"
include "eqtri.mm"

theorem fmtno1
  let vk: setvar k
  let vx: setvar x


  assert |- ( FermatNo ` 1 ) = 5

  proof
    c1
    cfmtno
    cfv
    #
    c2
    c2
    c1
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
    c5
    c1
    cn0
    wcel
    @0
    @3
    wceq
    1nn0
    c1
    fmtno
    ax-mp
    @3
    c2
    c2
    cexp
    co
    #
    c1
    caddc
    co
    c4
    c1
    caddc
    co
    c5
    @2
    @4
    c1
    caddc
    @1
    c2
    c2
    cexp
    c2
    cc
    wcel
    @1
    c2
    wceq
    2cn
    c2
    exp1
    ax-mp
    oveq2i
    oveq1i
    @4
    c4
    c1
    caddc
    sq2
    oveq1i
    4p1e5
    3eqtri
    eqtri
end
