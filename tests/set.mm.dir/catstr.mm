include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "chom.mm"
include "cco.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "c5.mm"
include "1nn.mm"
include "basendx.mm"
include "4nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "4nn.mm"
include "decnncl.mm"
include "homndx.mm"
include "5nn.mm"
include "4lt5.mm"
include "declt.mm"
include "ccondx.mm"
include "strle3.mm"

theorem catstr
  let c.x: class .x.
  let cU: class U
  let cH: class H


  assert |- { <. ( Base ` ndx ) , U >. , <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } Struct <. 1 , ; 1 5 >.

  proof
    cnx
    cbs
    cfv
    cnx
    chom
    cfv
    cnx
    cco
    cfv
    c1
    c1
    c4
    cdc
    c1
    c5
    cdc
    cU
    cH
    c.x
    1nn
    basendx
    c1
    c4
    c1
    1nn
    4nn0
    1nn0
    1lt10
    declti
    c1
    c4
    1nn0
    4nn
    decnncl
    homndx
    c1
    c4
    c5
    1nn0
    4nn0
    5nn
    4lt5
    declt
    c1
    c5
    1nn0
    5nn
    decnncl
    ccondx
    strle3
end
