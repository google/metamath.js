include "con0.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "csuc.mm"
include "suceloni.mm"
include "fmpti.mm"
include "wcel.mm"
include "wa.mm"
include "fin1a2lem1.mm"
include "eqeqan12d.mm"
include "suc11.mm"
include "bitrd.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"

theorem fin1a2lem2
  let vx: setvar x
  let cS: class S
  let va: setvar a
  let cA: class A
  let vb: setvar b
  assume fin1a2lem.a: |- S = ( x e. On |-> suc x )


  assert |- S : On -1-1-> On

  proof
    con0
    con0
    cS
    wf1
    con0
    con0
    cS
    wf
    va
    cv
    #
    cS
    cfv
    #
    vb
    cv
    #
    cS
    cfv
    #
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    con0
    wral
    va
    con0
    wral
    vx
    con0
    con0
    vx
    cv
    #
    csuc
    cS
    fin1a2lem.a
    @7
    suceloni
    fmpti
    @6
    va
    vb
    con0
    @0
    con0
    wcel
    #
    @2
    con0
    wcel
    #
    wa
    #
    @4
    @5
    @10
    @4
    @0
    csuc
    #
    @2
    csuc
    #
    wceq
    @5
    @8
    @9
    @1
    @11
    @3
    @12
    vx
    @0
    cS
    fin1a2lem.a
    fin1a2lem1
    vx
    @2
    cS
    fin1a2lem.a
    fin1a2lem1
    eqeqan12d
    @0
    @2
    suc11
    bitrd
    biimpd
    rgen2a
    va
    vb
    con0
    con0
    cS
    dff13
    mpbir2an
end
