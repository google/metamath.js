include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "cuni.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "wa.mm"
include "istopg.mm"
include "ibi.mm"
include "simpld.mm"
include "cpw.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "wceq.mm"
include "sseq1.mm"
include "unieq.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl.mm"
include "com23.mm"
include "ex.mm"
include "pm2.43d.mm"
include "mpid.mm"
include "imp.mm"

theorem uniopn
  let cA: class A
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( J e. Top /\ A C_ J ) -> U. A e. J )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cJ
    wss
    #
    cA
    cuni
    #
    cJ
    wcel
    #
    @0
    @1
    vx
    cv
    #
    cJ
    wss
    #
    @4
    cuni
    #
    cJ
    wcel
    #
    wi
    #
    vx
    wal
    #
    @3
    @0
    @9
    @4
    vy
    cv
    cin
    cJ
    wcel
    vy
    cJ
    wral
    vx
    cJ
    wral
    #
    @0
    @9
    @10
    wa
    vx
    vy
    ctop
    cJ
    istopg
    ibi
    simpld
    @0
    @1
    @9
    @3
    wi
    #
    @0
    @1
    @1
    @11
    wi
    @0
    @1
    wa
    #
    @9
    @1
    @3
    @12
    cA
    cJ
    cpw
    #
    wcel
    #
    @9
    @1
    @3
    wi
    #
    wi
    @0
    @14
    @1
    cA
    cJ
    ctop
    elpw2g
    biimpar
    @8
    @15
    vx
    cA
    @13
    @4
    cA
    wceq
    #
    @5
    @1
    @7
    @3
    @4
    cA
    cJ
    sseq1
    @16
    @6
    @2
    cJ
    @4
    cA
    unieq
    eleq1d
    imbi12d
    spcgv
    syl
    com23
    ex
    pm2.43d
    mpid
    imp
end
