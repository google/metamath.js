include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c3.mm"
include "cmin.mm"
include "cmul.mm"
include "c6.mm"
include "2cn.mm"
include "3cn.mm"
include "2ne0.mm"
include "3ne0.mm"
include "subreci.mm"
include "ax-1cn.mm"
include "2p1e3.mm"
include "subaddrii.mm"
include "3t2e6.mm"
include "mulcomli.mm"
include "oveq12i.mm"
include "eqtri.mm"

theorem halfthird



  assert |- ( ( 1 / 2 ) - ( 1 / 3 ) ) = ( 1 / 6 )

  proof
    c1
    c2
    cdiv
    co
    c1
    c3
    cdiv
    co
    cmin
    co
    c3
    c2
    cmin
    co
    #
    c2
    c3
    cmul
    co
    #
    cdiv
    co
    c1
    c6
    cdiv
    co
    c2
    c3
    2cn
    3cn
    2ne0
    3ne0
    subreci
    @0
    c1
    @1
    c6
    cdiv
    c3
    c2
    c1
    3cn
    2cn
    ax-1cn
    2p1e3
    subaddrii
    c3
    c2
    c6
    3cn
    2cn
    3t2e6
    mulcomli
    oveq12i
    eqtri
end
