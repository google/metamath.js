include "c4.mm"
include "cfmtno.mm"
include "cfv.mm"
include "csqrt.mm"
include "cfl.mm"
include "c2.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "c5.mm"
include "cdc.mm"
include "c6.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "4nn.mm"
include "fmtnosqrt.mm"
include "ax-mp.mm"
include "c8.mm"
include "c3.mm"
include "4m1e3.mm"
include "oveq2i.mm"
include "cu2.mm"
include "eqtri.mm"
include "2exp8.mm"

theorem fmtno4sqrt
  let vk: setvar k
  let vx: setvar x


  assert |- ( |_ ` ( sqrt ` ( FermatNo ` 4 ) ) ) = ; ; 2 5 6

  proof
    c4
    cfmtno
    cfv
    csqrt
    cfv
    cfl
    cfv
    #
    c2
    c2
    c4
    c1
    cmin
    co
    #
    cexp
    co
    #
    cexp
    co
    #
    c2
    c5
    cdc
    c6
    cdc
    #
    c4
    cn
    wcel
    @0
    @3
    wceq
    4nn
    c4
    fmtnosqrt
    ax-mp
    @3
    c2
    c8
    cexp
    co
    @4
    @2
    c8
    c2
    cexp
    @2
    c2
    c3
    cexp
    co
    c8
    @1
    c3
    c2
    cexp
    4m1e3
    oveq2i
    cu2
    eqtri
    oveq2i
    2exp8
    eqtri
    eqtri
end
