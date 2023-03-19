include "c4.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cbc.mm"
include "c3.mm"
include "4cn.mm"
include "ax-1cn.mm"
include "3cn.mm"
include "3p1e4.mm"
include "addcomli.mm"
include "subaddrii.mm"
include "oveq2i.mm"
include "cn0.mm"
include "wcel.mm"
include "wceq.mm"
include "4nn0.mm"
include "bcnm1.mm"
include "ax-mp.mm"
include "eqtr3i.mm"

theorem 4bc3eq4



  assert |- ( 4 _C 3 ) = 4

  proof
    c4
    c4
    c1
    cmin
    co
    #
    cbc
    co
    #
    c4
    c3
    cbc
    co
    c4
    @0
    c3
    c4
    cbc
    c4
    c1
    c3
    4cn
    ax-1cn
    3cn
    c3
    c1
    c4
    3cn
    ax-1cn
    3p1e4
    addcomli
    subaddrii
    oveq2i
    c4
    cn0
    wcel
    @1
    c4
    wceq
    4nn0
    c4
    bcnm1
    ax-mp
    eqtr3i
end
