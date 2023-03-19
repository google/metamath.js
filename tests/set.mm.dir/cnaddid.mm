include "cc0.mm"
include "c0g.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "0cn.mm"
include "caddc.mm"
include "cvv.mm"
include "cbs.mm"
include "cnex.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "eqid.mm"
include "cplusg.mm"
include "addex.mm"
include "grpplusg.mm"
include "id.mm"
include "cv.mm"
include "co.mm"
include "addid2.mm"
include "adantl.mm"
include "addid1.mm"
include "ismgmid2.mm"
include "eqcomi.mm"

theorem cnaddid
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cnaddabl.g: |- G = { <. ( Base ` ndx ) , CC >. , <. ( +g ` ndx ) , + >. }


  assert |- ( 0g ` G ) = 0

  proof
    cc0
    cG
    c0g
    cfv
    #
    cc0
    cc
    wcel
    #
    cc0
    @0
    wceq
    0cn
    @1
    vx
    cc
    caddc
    cc0
    cG
    @0
    cc
    cvv
    wcel
    cc
    cG
    cbs
    cfv
    wceq
    cnex
    cc
    caddc
    cG
    cvv
    cnaddabl.g
    grpbase
    ax-mp
    @0
    eqid
    caddc
    cvv
    wcel
    caddc
    cG
    cplusg
    cfv
    wceq
    addex
    cc
    caddc
    cG
    cvv
    cnaddabl.g
    grpplusg
    ax-mp
    @1
    id
    vx
    cv
    #
    cc
    wcel
    #
    cc0
    @2
    caddc
    co
    @2
    wceq
    @1
    @2
    addid2
    adantl
    @3
    @2
    cc0
    caddc
    co
    @2
    wceq
    @1
    @2
    addid1
    adantl
    ismgmid2
    ax-mp
    eqcomi
end
