include "cno.mm"
include "csp.mm"
include "cdm.mm"
include "cv.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmpt.mm"
include "chil.mm"
include "df-hnorm.mm"
include "cxp.mm"
include "cc.mm"
include "ax-hfi.mm"
include "fdmi.mm"
include "dmeqi.mm"
include "dmxpid.mm"
include "eqtr2i.mm"
include "eqid.mm"
include "mpteq12i.mm"
include "eqtr4i.mm"

theorem dfhnorm2
  let vx: setvar x


  assert |- normh = ( x e. ~H |-> ( sqrt ` ( x .ih x ) ) )

  proof
    cno
    vx
    csp
    cdm
    #
    cdm
    #
    vx
    cv
    #
    @2
    csp
    co
    csqrt
    cfv
    #
    cmpt
    vx
    chil
    @3
    cmpt
    vx
    df-hnorm
    vx
    chil
    @3
    @1
    @3
    @1
    chil
    chil
    cxp
    #
    cdm
    chil
    @0
    @4
    @4
    cc
    csp
    ax-hfi
    fdmi
    dmeqi
    chil
    dmxpid
    eqtr2i
    @3
    eqid
    mpteq12i
    eqtr4i
end
