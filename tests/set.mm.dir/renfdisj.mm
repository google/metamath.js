include "cr.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cpr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "disj.mm"
include "renepnf.mm"
include "renemnf.mm"
include "nelprd.mm"
include "mprgbir.mm"

theorem renfdisj
  let vx: setvar x


  assert |- ( RR i^i { +oo , -oo } ) = (/)

  proof
    cr
    cpnf
    cmnf
    cpr
    #
    cin
    c0
    wceq
    vx
    cv
    #
    @0
    wcel
    wn
    vx
    cr
    vx
    cr
    @0
    disj
    @1
    cr
    wcel
    @1
    cpnf
    cmnf
    @1
    renepnf
    @1
    renemnf
    nelprd
    mprgbir
end
