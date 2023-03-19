include "con0.mm"
include "cale.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "alephfnon.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "weq.mm"
include "com.mm"
include "aleph0.mm"
include "omelon.mm"
include "eqeltri.mm"
include "char.mm"
include "alephsuc.mm"
include "harcl.mm"
include "syl6eqel.mm"
include "a1d.mm"
include "wlim.mm"
include "ciun.mm"
include "cvv.mm"
include "vex.mm"
include "iunon.mm"
include "mpan.mm"
include "alephlim.mm"
include "syl5ibr.mm"
include "tfinds.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "0elon.mm"
include "f0cli.mm"

theorem alephon
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( aleph ` A ) e. On

  proof
    con0
    con0
    cA
    cale
    con0
    con0
    cale
    wf
    cale
    con0
    wfn
    vy
    cv
    #
    cale
    cfv
    #
    con0
    wcel
    #
    vy
    con0
    wral
    alephfnon
    @2
    vy
    con0
    vx
    cv
    #
    cale
    cfv
    #
    con0
    wcel
    #
    c0
    cale
    cfv
    #
    con0
    wcel
    @2
    @0
    csuc
    #
    cale
    cfv
    #
    con0
    wcel
    #
    @2
    vx
    vy
    @0
    @3
    c0
    wceq
    @4
    @6
    con0
    @3
    c0
    cale
    fveq2
    eleq1d
    vx
    vy
    weq
    @4
    @1
    con0
    @3
    @0
    cale
    fveq2
    eleq1d
    #
    @3
    @7
    wceq
    @4
    @8
    con0
    @3
    @7
    cale
    fveq2
    eleq1d
    @10
    @6
    com
    con0
    aleph0
    omelon
    eqeltri
    @0
    con0
    wcel
    #
    @9
    @2
    @11
    @8
    @1
    char
    cfv
    con0
    @0
    alephsuc
    @1
    harcl
    syl6eqel
    a1d
    @2
    vy
    @3
    wral
    #
    @5
    @3
    wlim
    #
    vy
    @3
    @1
    ciun
    #
    con0
    wcel
    #
    @3
    cvv
    wcel
    #
    @12
    @15
    vx
    vex
    #
    vy
    @3
    @1
    cvv
    iunon
    mpan
    @13
    @4
    @14
    con0
    @16
    @13
    @4
    @14
    wceq
    @17
    vy
    @3
    cvv
    alephlim
    mpan
    eleq1d
    syl5ibr
    tfinds
    rgen
    vy
    con0
    con0
    cale
    ffnfv
    mpbir2an
    0elon
    f0cli
end
