include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cts.mm"
include "cple.mm"
include "ctp.mm"
include "c1.mm"
include "c10.mm"
include "cstr.mm"
include "c9.mm"
include "1nn.mm"
include "basendx.mm"
include "1lt9.mm"
include "9nn.mm"
include "tsetndx.mm"
include "9lt10OLD.mm"
include "10nnOLD.mm"
include "plendxOLD.mm"
include "strle3.mm"
include "eqbrtri.mm"

theorem otpsstrOLD
  let cB: class B
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  assume otpsstr.w: |- K = { <. ( Base ` ndx ) , B >. , <. ( TopSet ` ndx ) , J >. , <. ( le ` ndx ) , .<_ >. }


  assert |- K Struct <. 1 , 10 >.

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
    c10
    cop
    cstr
    otpsstr.w
    @0
    @1
    @2
    c1
    c9
    c10
    cB
    cJ
    c.le
    1nn
    basendx
    1lt9
    9nn
    tsetndx
    9lt10OLD
    10nnOLD
    plendxOLD
    strle3
    eqbrtri
end
