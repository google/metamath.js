include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cfi.mm"
include "cfv.mm"
include "wfo.mm"
include "crn.mm"
include "wfn.mm"
include "cv.mm"
include "cint.mm"
include "cvv.mm"
include "wral.mm"
include "wne.mm"
include "eldifsni.mm"
include "intex.mm"
include "sylib.mm"
include "rgen.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "dffn4.mm"
include "wceq.mm"
include "wb.mm"
include "wrex.mm"
include "elfi2.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "foeq3.mm"
include "syl.mm"
include "mpbird.mm"

theorem fifo
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cV: class V
  let vx: setvar x
  assume fifo.1: |- F = ( y e. ( ( ~P A i^i Fin ) \ { (/) } ) |-> |^| y )

  disjoint A y
  disjoint V y
  disjoint x y
  disjoint A x
  disjoint F x
  disjoint V x
  assert |- ( A e. V -> F : ( ( ~P A i^i Fin ) \ { (/) } ) -onto-> ( fi ` A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    cfn
    cin
    #
    c0
    csn
    cdif
    #
    cA
    cfi
    cfv
    #
    cF
    wfo
    #
    @2
    cF
    crn
    #
    cF
    wfo
    #
    @0
    cF
    @2
    wfn
    #
    @6
    vy
    cv
    #
    cint
    #
    cvv
    wcel
    #
    vy
    @2
    wral
    @7
    @0
    @10
    vy
    @2
    @8
    @2
    wcel
    @8
    c0
    wne
    @10
    @8
    @1
    c0
    eldifsni
    @8
    intex
    sylib
    rgen
    vy
    @2
    @9
    cF
    cvv
    fifo.1
    fnmpt
    mp1i
    @2
    cF
    dffn4
    sylib
    @0
    @3
    @5
    wceq
    @4
    @6
    wb
    @0
    vx
    @3
    @5
    @0
    vx
    cv
    #
    @3
    wcel
    @11
    @9
    wceq
    vy
    @2
    wrex
    #
    @11
    @5
    wcel
    #
    vy
    @11
    cA
    cV
    elfi2
    @11
    cvv
    wcel
    @13
    @12
    wb
    vx
    vex
    vy
    @2
    @9
    @11
    cF
    cvv
    fifo.1
    elrnmpt
    ax-mp
    syl6bbr
    eqrdv
    @3
    @5
    @2
    cF
    foeq3
    syl
    mpbird
end
