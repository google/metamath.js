include "cho.mm"
include "wcel.mm"
include "clo.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "cbo.mm"
include "hmoplin.mm"
include "hmop.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "cva.mm"
include "csm.mm"
include "cop.mm"
include "cno.mm"
include "chlo.mm"
include "hilhl.mm"
include "df-hba.mm"
include "eqid.mm"
include "hhip.mm"
include "clno.mm"
include "hhlnoi.mm"
include "cblo.mm"
include "hhbloi.mm"
include "htth.mm"
include "mp3an1.mm"
include "syl2anc.mm"

theorem hmopbdoptHIL
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( T e. HrmOp -> T e. BndLinOp )

  proof
    cT
    cho
    wcel
    #
    cT
    clo
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    csp
    co
    @2
    cT
    cfv
    @3
    csp
    co
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    cT
    cbo
    wcel
    #
    cT
    hmoplin
    @0
    @4
    vx
    vy
    chil
    chil
    @0
    @2
    chil
    wcel
    @3
    chil
    wcel
    @4
    @2
    @3
    cT
    hmop
    3expib
    ralrimivv
    cva
    csm
    cop
    cno
    cop
    #
    chlo
    wcel
    @1
    @5
    @6
    hilhl
    vx
    vy
    cbo
    csp
    cT
    @7
    clo
    chil
    df-hba
    @7
    @7
    eqid
    #
    hhip
    @7
    @7
    @7
    clno
    co
    #
    @8
    @9
    eqid
    hhlnoi
    @7
    @7
    cblo
    co
    #
    @7
    @8
    @10
    eqid
    hhbloi
    htth
    mp3an1
    syl2anc
end
