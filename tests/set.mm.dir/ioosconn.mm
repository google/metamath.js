include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cioo.mm"
include "wss.mm"
include "wral.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "crest.mm"
include "csconn.mm"
include "wcel.mm"
include "iccssioo2.mm"
include "rgen2a.mm"
include "cr.mm"
include "wb.mm"
include "ioossre.mm"
include "cconn.mm"
include "eqid.mm"
include "resconn.mm"
include "reconn.mm"
include "bitr2d.mm"
include "ax-mp.mm"
include "mpbi.mm"

theorem ioosconn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( topGen ` ran (,) ) |`t ( A (,) B ) ) e. SConn

  proof
    vx
    cv
    #
    vy
    cv
    #
    cicc
    co
    cA
    cB
    cioo
    co
    #
    wss
    #
    vy
    @2
    wral
    vx
    @2
    wral
    #
    cioo
    crn
    ctg
    cfv
    @2
    crest
    co
    #
    csconn
    wcel
    #
    @3
    vx
    vy
    @2
    cA
    cB
    @0
    @1
    iccssioo2
    rgen2a
    @2
    cr
    wss
    #
    @4
    @6
    wb
    cA
    cB
    ioossre
    @7
    @6
    @5
    cconn
    wcel
    @4
    @2
    @5
    @5
    eqid
    resconn
    vx
    vy
    @2
    reconn
    bitr2d
    ax-mp
    mpbi
end
