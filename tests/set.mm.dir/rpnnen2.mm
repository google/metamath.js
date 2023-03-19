include "cn.mm"
include "cpw.mm"
include "wel.mm"
include "c1.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "rpnnen2lem12.mm"

theorem rpnnen2
  let vn: setvar n
  let vx: setvar x


  assert |- ~P NN ~<_ ( 0 [,] 1 )

  proof
    vx
    vn
    vx
    cn
    cpw
    vn
    cn
    vn
    vx
    wel
    c1
    c3
    cdiv
    co
    vn
    cv
    cexp
    co
    cc0
    cif
    cmpt
    cmpt
    #
    @0
    eqid
    rpnnen2lem12
end
