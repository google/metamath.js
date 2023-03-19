include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "cdif.mm"
include "wcel.mm"
include "cpw.mm"
include "crab.mm"
include "ccld.mm"
include "vuniex.mm"
include "pwex.mm"
include "rabex.mm"
include "df-cld.mm"
include "fnmpti.mm"

theorem fncld
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y


  assert |- Clsd Fn Top

  proof
    vj
    ctop
    vj
    cv
    #
    cuni
    #
    vx
    cv
    cdif
    @0
    wcel
    #
    vx
    @1
    cpw
    #
    crab
    ccld
    @2
    vx
    @3
    @1
    vj
    vuniex
    pwex
    rabex
    vx
    vj
    df-cld
    fnmpti
end
