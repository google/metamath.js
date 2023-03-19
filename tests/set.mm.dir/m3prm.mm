include "c2.mm"
include "c3.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "c7.mm"
include "cprime.mm"
include "c8.mm"
include "cu2.mm"
include "oveq1i.mm"
include "wceq.mm"
include "caddc.mm"
include "7p1e8.mm"
include "8cn.mm"
include "ax-1cn.mm"
include "7cn.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "eqtri.mm"
include "7prm.mm"
include "eqeltri.mm"

theorem m3prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( 2 ^ 3 ) - 1 ) e. Prime

  proof
    c2
    c3
    cexp
    co
    #
    c1
    cmin
    co
    #
    c7
    cprime
    @1
    c8
    c1
    cmin
    co
    #
    c7
    @0
    c8
    c1
    cmin
    cu2
    oveq1i
    @2
    c7
    wceq
    c7
    c1
    caddc
    co
    c8
    wceq
    7p1e8
    c8
    c1
    c7
    8cn
    ax-1cn
    7cn
    subadd2i
    mpbir
    eqtri
    7prm
    eqeltri
end
