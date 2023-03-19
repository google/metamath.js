include "cioo.mm"
include "co.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wcel.mm"
include "cnt.mm"
include "wceq.mm"
include "iooretop.mm"
include "ctop.mm"
include "cr.mm"
include "wss.mm"
include "wb.mm"
include "retop.mm"
include "ioossre.mm"
include "uniretop.mm"
include "isopn3.mm"
include "mp2an.mm"
include "mpbi.mm"

theorem ioontr
  let cA: class A
  let cB: class B


  assert |- ( ( int ` ( topGen ` ran (,) ) ) ` ( A (,) B ) ) = ( A (,) B )

  proof
    cA
    cB
    cioo
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    wcel
    #
    @0
    @1
    cnt
    cfv
    cfv
    @0
    wceq
    #
    cA
    cB
    iooretop
    @1
    ctop
    wcel
    @0
    cr
    wss
    @2
    @3
    wb
    retop
    cA
    cB
    ioossre
    @0
    @1
    cr
    uniretop
    isopn3
    mp2an
    mpbi
end
