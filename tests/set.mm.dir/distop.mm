include "wcel.mm"
include "cpw.mm"
include "ctop.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "wral.mm"
include "uniss.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "vuniex.mm"
include "elpw.mm"
include "sylibr.mm"
include "ax-gen.mm"
include "a1i.mm"
include "selpw.mm"
include "ssinss1.mm"
include "vex.mm"
include "inex2.mm"
include "syl6ibr.mm"
include "sylbi.mm"
include "com12.mm"
include "ralrimiv.mm"
include "rgen.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "pwexg.mm"
include "istopg.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem distop
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ~P A e. Top )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    ctop
    wcel
    #
    vx
    cv
    #
    @1
    wss
    #
    @3
    cuni
    #
    @1
    wcel
    #
    wi
    #
    vx
    wal
    #
    @3
    vy
    cv
    #
    cin
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    @8
    @0
    @7
    vx
    @4
    @5
    cA
    wss
    @6
    @4
    @5
    @1
    cuni
    cA
    @3
    @1
    uniss
    cA
    unipw
    syl6sseq
    @5
    cA
    vx
    vuniex
    elpw
    sylibr
    ax-gen
    a1i
    @13
    @0
    @12
    vx
    @1
    @3
    @1
    wcel
    #
    @11
    vy
    @1
    @14
    @3
    cA
    wss
    #
    @9
    @1
    wcel
    #
    @11
    wi
    vx
    cA
    selpw
    @16
    @15
    @11
    @16
    @9
    cA
    wss
    #
    @15
    @11
    wi
    vy
    cA
    selpw
    @17
    @15
    @10
    cA
    wss
    #
    @11
    @15
    @18
    wi
    @17
    @3
    @9
    cA
    ssinss1
    a1i
    @10
    cA
    @9
    @3
    vy
    vex
    inex2
    elpw
    syl6ibr
    sylbi
    com12
    sylbi
    ralrimiv
    rgen
    a1i
    @0
    @1
    cvv
    wcel
    @2
    @8
    @13
    wa
    wb
    cA
    cV
    pwexg
    vx
    vy
    cvv
    @1
    istopg
    syl
    mpbir2and
end
