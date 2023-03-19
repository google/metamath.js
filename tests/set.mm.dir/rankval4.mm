include "crnk.mm"
include "cfv.mm"
include "cv.mm"
include "csuc.mm"
include "ciun.mm"
include "cr1.mm"
include "wss.mm"
include "wcel.mm"
include "wi.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nffv.mm"
include "dfss2f.mm"
include "vex.mm"
include "rankid.mm"
include "ssiun2.mm"
include "con0.mm"
include "rankon.mm"
include "onsuci.mm"
include "cvv.mm"
include "wral.mm"
include "rgenw.mm"
include "iunon.mm"
include "mp2an.mm"
include "r1ord3.mm"
include "syl.mm"
include "sseld.mm"
include "mpi.mm"
include "mpgbir.mm"
include "fvex.mm"
include "rankss.mm"
include "ax-mp.mm"
include "crab.mm"
include "cint.mm"
include "mpan.mm"
include "ss2rabi.mm"
include "intss.mm"
include "wceq.mm"
include "rankval2.mm"
include "intmin.mm"
include "eqcomi.mm"
include "3sstr4i.mm"
include "sstri.mm"
include "iunss.mm"
include "rankel.mm"
include "onsucssi.mm"
include "sylib.mm"
include "mprgbir.mm"
include "eqssi.mm"

theorem rankval4
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B
  assume rankr1b.1: |- A e. _V

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( rank ` A ) = U_ x e. A suc ( rank ` x )

  proof
    cA
    crnk
    cfv
    #
    vx
    cA
    vx
    cv
    #
    crnk
    cfv
    #
    csuc
    #
    ciun
    #
    @0
    @4
    cr1
    cfv
    #
    crnk
    cfv
    #
    @4
    cA
    @5
    wss
    #
    @0
    @6
    wss
    @7
    @1
    cA
    wcel
    #
    @1
    @5
    wcel
    #
    wi
    vx
    vx
    cA
    @5
    vx
    cA
    nfcv
    vx
    @4
    cr1
    vx
    cr1
    nfcv
    vx
    cA
    @3
    nfiu1
    nffv
    dfss2f
    @8
    @1
    @3
    cr1
    cfv
    #
    wcel
    @9
    @1
    vx
    vex
    rankid
    @8
    @10
    @5
    @1
    @8
    @3
    @4
    wss
    #
    @10
    @5
    wss
    #
    vx
    cA
    @3
    ssiun2
    @3
    con0
    wcel
    #
    @4
    con0
    wcel
    #
    @11
    @12
    wi
    @2
    @1
    rankon
    #
    onsuci
    #
    cA
    cvv
    wcel
    @13
    vx
    cA
    wral
    @14
    rankr1b.1
    @13
    vx
    cA
    @16
    rgenw
    vx
    cA
    @3
    cvv
    iunon
    mp2an
    #
    @3
    @4
    r1ord3
    mp2an
    syl
    sseld
    mpi
    mpgbir
    cA
    @5
    @4
    cr1
    fvex
    #
    rankss
    ax-mp
    @5
    vy
    cv
    #
    cr1
    cfv
    wss
    #
    vy
    con0
    crab
    #
    cint
    #
    @4
    @19
    wss
    #
    vy
    con0
    crab
    #
    cint
    #
    @6
    @4
    @24
    @21
    wss
    @22
    @25
    wss
    @23
    @20
    vy
    con0
    @14
    @19
    con0
    wcel
    @23
    @20
    wi
    @17
    @4
    @19
    r1ord3
    mpan
    ss2rabi
    @24
    @21
    intss
    ax-mp
    @5
    cvv
    wcel
    @6
    @22
    wceq
    @18
    vy
    @5
    cvv
    rankval2
    ax-mp
    @25
    @4
    @14
    @25
    @4
    wceq
    @17
    vy
    @4
    con0
    intmin
    ax-mp
    eqcomi
    3sstr4i
    sstri
    @4
    @0
    wss
    @3
    @0
    wss
    #
    vx
    cA
    vx
    cA
    @3
    @0
    iunss
    @8
    @2
    @0
    wcel
    @26
    @1
    cA
    rankr1b.1
    rankel
    @2
    @0
    @15
    cA
    rankon
    onsucssi
    sylib
    mprgbir
    eqssi
end
