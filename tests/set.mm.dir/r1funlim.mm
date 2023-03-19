include "cr1.mm"
include "wfun.mm"
include "cdm.mm"
include "wlim.mm"
include "cvv.mm"
include "cv.mm"
include "cpw.mm"
include "cmpt.mm"
include "c0.mm"
include "crdg.mm"
include "rdgfun.mm"
include "df-r1.mm"
include "funeqi.mm"
include "mpbir.mm"
include "rdgdmlim.mm"
include "wceq.mm"
include "wb.mm"
include "dmeqi.mm"
include "limeq.mm"
include "ax-mp.mm"
include "pm3.2i.mm"

theorem r1funlim
  let vx: setvar x


  assert |- ( Fun R1 /\ Lim dom R1 )

  proof
    cr1
    wfun
    #
    cr1
    cdm
    #
    wlim
    #
    @0
    vx
    cvv
    vx
    cv
    cpw
    cmpt
    #
    c0
    crdg
    #
    wfun
    c0
    @3
    rdgfun
    cr1
    @4
    vx
    df-r1
    #
    funeqi
    mpbir
    @2
    @4
    cdm
    #
    wlim
    #
    c0
    @3
    rdgdmlim
    @1
    @6
    wceq
    @2
    @7
    wb
    cr1
    @4
    @5
    dmeqi
    @1
    @6
    limeq
    ax-mp
    mpbir
    pm3.2i
end
