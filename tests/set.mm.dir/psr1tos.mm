include "ctos.mm"
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
include "wwe.mm"
include "0we1.mm"
include "opsrtos.mm"

theorem psr1tos
  let cR: class R
  let cS: class S
  let vr: setvar r
  assume psr1val.1: |- S = ( PwSer1 ` R )


  assert |- ( R e. Toset -> S e. Toset )

  proof
    cR
    ctos
    wcel
    #
    cR
    c0
    c1o
    cS
    con0
    cR
    cS
    psr1val.1
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
    c1o
    c0
    wwe
    @0
    0we1
    a1i
    opsrtos
end
