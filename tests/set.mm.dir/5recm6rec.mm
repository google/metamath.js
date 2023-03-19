include "c1.mm"
include "c5.mm"
include "cdiv.mm"
include "co.mm"
include "c6.mm"
include "cmin.mm"
include "cmul.mm"
include "c3.mm"
include "cc0.mm"
include "cdc.mm"
include "5cn.mm"
include "6cn.mm"
include "5re.mm"
include "5pos.mm"
include "gt0ne0ii.mm"
include "6re.mm"
include "6pos.mm"
include "subreci.mm"
include "ax-1cn.mm"
include "5p1e6.mm"
include "subaddrii.mm"
include "6t5e30.mm"
include "mulcomli.mm"
include "oveq12i.mm"
include "eqtri.mm"

theorem 5recm6rec



  assert |- ( ( 1 / 5 ) - ( 1 / 6 ) ) = ( 1 / ; 3 0 )

  proof
    c1
    c5
    cdiv
    co
    c1
    c6
    cdiv
    co
    cmin
    co
    c6
    c5
    cmin
    co
    #
    c5
    c6
    cmul
    co
    #
    cdiv
    co
    c1
    c3
    cc0
    cdc
    #
    cdiv
    co
    c5
    c6
    5cn
    6cn
    c5
    5re
    5pos
    gt0ne0ii
    c6
    6re
    6pos
    gt0ne0ii
    subreci
    @0
    c1
    @1
    @2
    cdiv
    c6
    c5
    c1
    6cn
    5cn
    ax-1cn
    5p1e6
    subaddrii
    c6
    c5
    @2
    6cn
    5cn
    6t5e30
    mulcomli
    oveq12i
    eqtri
end
