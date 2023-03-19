include "c1.mm"
include "c9.mm"
include "cc0.mm"
include "cdc.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cts.mm"
include "cpr.mm"
include "cple.mm"
include "coc.mm"
include "1nn.mm"
include "basendx.mm"
include "1lt9.mm"
include "9nn.mm"
include "tsetndx.mm"
include "strle2.mm"
include "10nn.mm"
include "plendx.mm"
include "1nn0.mm"
include "0nn0.mm"
include "0lt1.mm"
include "declt.mm"
include "decnncl.mm"
include "ocndx.mm"
include "9lt10.mm"
include "strleun.mm"

theorem ipostr
  let cB: class B
  let cJ: class J
  let c.le: class .<_
  let c.pe: class ._|_


  assert |- ( { <. ( Base ` ndx ) , B >. , <. ( TopSet ` ndx ) , J >. } u. { <. ( le ` ndx ) , .<_ >. , <. ( oc ` ndx ) , ._|_ >. } ) Struct <. 1 , ; 1 1 >.

  proof
    c1
    c9
    c1
    cc0
    cdc
    #
    c1
    c1
    cdc
    #
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
    cpr
    cnx
    cple
    cfv
    #
    c.le
    cop
    cnx
    coc
    cfv
    #
    c.pe
    cop
    cpr
    @2
    @3
    c1
    c9
    cB
    cJ
    1nn
    basendx
    1lt9
    9nn
    tsetndx
    strle2
    @4
    @5
    @0
    @1
    c.le
    c.pe
    10nn
    plendx
    c1
    cc0
    c1
    1nn0
    0nn0
    1nn
    0lt1
    declt
    c1
    c1
    1nn0
    1nn
    decnncl
    ocndx
    strle2
    9lt10
    strleun
end
