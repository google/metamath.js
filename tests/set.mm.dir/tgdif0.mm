include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "ctg.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "cab.mm"
include "indif1.mm"
include "unieqi.mm"
include "unidif0.mm"
include "eqtri.mm"
include "sseq2i.mm"
include "abbii.mm"
include "difexg.mm"
include "tgval.mm"
include "syl.mm"
include "3eqtr4a.mm"
include "wn.mm"
include "difsnexi.mm"
include "con3i.mm"
include "fvprc.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem tgdif0
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cJ: class J
  let cV: class V


  assert |- ( topGen ` ( B \ { (/) } ) ) = ( topGen ` B )

  proof
    cB
    cvv
    wcel
    #
    cB
    c0
    csn
    #
    cdif
    #
    ctg
    cfv
    #
    cB
    ctg
    cfv
    #
    wceq
    @0
    vx
    cv
    #
    @2
    @5
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vx
    cab
    #
    @5
    cB
    @6
    cin
    #
    cuni
    #
    wss
    #
    vx
    cab
    @3
    @4
    @9
    @13
    vx
    @8
    @12
    @5
    @8
    @11
    @1
    cdif
    #
    cuni
    @12
    @7
    @14
    cB
    @6
    @1
    indif1
    unieqi
    @11
    unidif0
    eqtri
    sseq2i
    abbii
    @0
    @2
    cvv
    wcel
    #
    @3
    @10
    wceq
    cB
    @1
    cvv
    difexg
    vx
    @2
    cvv
    tgval
    syl
    vx
    cB
    cvv
    tgval
    3eqtr4a
    @0
    wn
    #
    @3
    c0
    @4
    @16
    @15
    wn
    @3
    c0
    wceq
    @15
    @0
    c0
    cB
    difsnexi
    con3i
    @2
    ctg
    fvprc
    syl
    cB
    ctg
    fvprc
    eqtr4d
    pm2.61i
end
