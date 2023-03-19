include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cvv.mm"
include "wfo.mm"
include "cwdom.mm"
include "wbr.mm"
include "resiexg.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1ofo.mm"
include "ax-mp.mm"
include "fowdom.mm"
include "sylancl.mm"

theorem wdomref
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cY: class Y
  let cF: class F
  let cZ: class Z


  assert |- ( X e. V -> X ~<_* X )

  proof
    cX
    cV
    wcel
    cid
    cX
    cres
    #
    cvv
    wcel
    cX
    cX
    @0
    wfo
    #
    cX
    cX
    cwdom
    wbr
    cX
    cV
    resiexg
    cX
    cX
    @0
    wf1o
    @1
    cX
    f1oi
    cX
    cX
    @0
    f1ofo
    ax-mp
    @0
    cvv
    cX
    cX
    fowdom
    sylancl
end
