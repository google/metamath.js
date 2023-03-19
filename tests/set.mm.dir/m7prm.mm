include "c2.mm"
include "c7.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cdc.mm"
include "cprime.mm"
include "c8.mm"
include "c3.mm"
include "1nn0.mm"
include "2nn0.mm"
include "deccl.mm"
include "8nn0.mm"
include "2exp7.mm"
include "2p1e3.mm"
include "eqid.mm"
include "decsuc.mm"
include "wceq.mm"
include "caddc.mm"
include "7p1e8.mm"
include "8cn.mm"
include "ax-1cn.mm"
include "7cn.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "decsubi.mm"
include "127prm.mm"
include "eqeltri.mm"

theorem m7prm
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( 2 ^ 7 ) - 1 ) e. Prime

  proof
    c2
    c7
    cexp
    co
    #
    c1
    cmin
    co
    c1
    c2
    cdc
    #
    c7
    cdc
    cprime
    @1
    c8
    c7
    c1
    c3
    cdc
    @0
    c1
    c1
    c2
    1nn0
    2nn0
    deccl
    8nn0
    1nn0
    2exp7
    c1
    c2
    c3
    @1
    1nn0
    2nn0
    2p1e3
    @1
    eqid
    decsuc
    c8
    c1
    cmin
    co
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
    decsubi
    127prm
    eqeltri
end
