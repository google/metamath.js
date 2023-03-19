include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "crest.mm"
include "cconn.mm"
include "cv.mm"
include "wss.mm"
include "wral.mm"
include "iccss2.mm"
include "rgen2a.mm"
include "wb.mm"
include "iccssre.mm"
include "reconn.mm"
include "syl.mm"
include "mpbiri.mm"

theorem iccconn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( topGen ` ran (,) ) |`t ( A [,] B ) ) e. Conn )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    wa
    #
    cioo
    crn
    ctg
    cfv
    cA
    cB
    cicc
    co
    #
    crest
    co
    cconn
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cicc
    co
    @1
    wss
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    @5
    vx
    vy
    @1
    cA
    cB
    @3
    @4
    iccss2
    rgen2a
    @0
    @1
    cr
    wss
    @2
    @6
    wb
    cA
    cB
    iccssre
    vx
    vy
    @1
    reconn
    syl
    mpbiri
end
