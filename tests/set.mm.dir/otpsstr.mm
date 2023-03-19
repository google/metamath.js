include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cts.mm"
include "cple.mm"
include "ctp.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "cstr.mm"
include "c9.mm"
include "1nn.mm"
include "basendx.mm"
include "1lt9.mm"
include "9nn.mm"
include "tsetndx.mm"
include "9lt10.mm"
include "10nn.mm"
include "plendx.mm"
include "strle3.mm"
include "eqbrtri.mm"

theorem otpsstr
  let cB: class B
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  assume otpsstr.w: |- K = { <. ( Base ` ndx ) , B >. , <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. }


  assert |- K Struct <. 1 , ; 1 0 >.

  proof
    cK
    cnx
    cbs
    cfv
    #
    cB
    cop
    cnx
    cts
    cfv
    #
    cJ
    cop
    cnx
    cple
    cfv
    #
    c.le
    cop
    ctp
    c1
    c1
    cc0
    cdc
    #
    cop
    cstr
    otpsstr.w
    @0
    @1
    @2
    c1
    c9
    @3
    cB
    cJ
    c.le
    1nn
    basendx
    1lt9
    9nn
    tsetndx
    9lt10
    10nn
    plendx
    strle3
    eqbrtri
end
