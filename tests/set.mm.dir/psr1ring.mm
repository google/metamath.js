include "crg.mm"
include "wcel.mm"
include "c0.mm"
include "c1o.mm"
include "con0.mm"
include "psr1val.mm"
include "1on.mm"
include "a1i.mm"
include "id.mm"
include "cxp.mm"
include "wss.mm"
include "0ss.mm"
include "opsrring.mm"

theorem psr1ring
  let cR: class R
  let cS: class S
  assume psr1ring.s: |- S = ( PwSer1 ` R )


  assert |- ( R e. Ring -> S e. Ring )

  proof
    cR
    crg
    wcel
    #
    cR
    c0
    c1o
    cS
    con0
    cR
    cS
    psr1ring.s
    psr1val
    c1o
    con0
    wcel
    @0
    1on
    a1i
    @0
    id
    c0
    c1o
    c1o
    cxp
    #
    wss
    @0
    @1
    0ss
    a1i
    opsrring
end
