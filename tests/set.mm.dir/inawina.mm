include "c0.mm"
include "wne.mm"
include "ccf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wrex.mm"
include "cina.mm"
include "wcel.mm"
include "cwina.mm"
include "con0.mm"
include "cfon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "3ad2ant2.mm"
include "idd.mm"
include "inawinalem.mm"
include "3anim123d.mm"
include "mpcom.mm"
include "elina.mm"
include "elwina.mm"
include "3imtr4i.mm"

theorem inawina
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. Inacc -> A e. InaccW )

  proof
    cA
    c0
    wne
    #
    cA
    ccf
    cfv
    #
    cA
    wceq
    #
    vx
    cv
    #
    cpw
    cA
    csdm
    wbr
    vx
    cA
    wral
    #
    w3a
    #
    @0
    @2
    @3
    vy
    cv
    csdm
    wbr
    vy
    cA
    wrex
    vx
    cA
    wral
    #
    w3a
    #
    cA
    cina
    wcel
    cA
    cwina
    wcel
    cA
    con0
    wcel
    #
    @5
    @7
    @2
    @0
    @8
    @4
    @2
    @1
    con0
    wcel
    @8
    cA
    cfon
    @1
    cA
    con0
    eleq1
    mpbii
    3ad2ant2
    @8
    @0
    @0
    @2
    @2
    @4
    @6
    @8
    @0
    idd
    @8
    @2
    idd
    vx
    vy
    cA
    inawinalem
    3anim123d
    mpcom
    vx
    cA
    elina
    vx
    vy
    cA
    elwina
    3imtr4i
end
