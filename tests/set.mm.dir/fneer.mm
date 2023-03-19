include "cv.mm"
include "ctg.mm"
include "cfv.mm"
include "fveq2.mm"
include "wbr.mm"
include "copab.mm"
include "wceq.mm"
include "wrel.mm"
include "cfne.mm"
include "wss.mm"
include "ccnv.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstri.mm"
include "fnerel.mm"
include "relss.mm"
include "mp2.mm"
include "dfrel4v.mm"
include "mpbi.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "vex.mm"
include "fneval.mm"
include "mp2an.mm"
include "opabbii.mm"
include "eqtri.mm"
include "eqer.mm"

theorem fneer
  let c.sm: class .~
  let vx: setvar x
  let vy: setvar y
  assume fneval.1: |- .~ = ( Fne i^i `' Fne )


  assert |- .~ Er _V

  proof
    vx
    vy
    vx
    cv
    #
    ctg
    cfv
    #
    vy
    cv
    #
    ctg
    cfv
    #
    c.sm
    @0
    @2
    ctg
    fveq2
    c.sm
    @0
    @2
    c.sm
    wbr
    #
    vx
    vy
    copab
    #
    @1
    @3
    wceq
    #
    vx
    vy
    copab
    c.sm
    wrel
    #
    c.sm
    @5
    wceq
    c.sm
    cfne
    wss
    cfne
    wrel
    @7
    c.sm
    cfne
    cfne
    ccnv
    #
    cin
    cfne
    fneval.1
    cfne
    @8
    inss1
    eqsstri
    fnerel
    c.sm
    cfne
    relss
    mp2
    vx
    vy
    c.sm
    dfrel4v
    mpbi
    @4
    @6
    vx
    vy
    @0
    cvv
    wcel
    @2
    cvv
    wcel
    @4
    @6
    wb
    vx
    vex
    vy
    vex
    @0
    @2
    c.sm
    cvv
    cvv
    fneval.1
    fneval
    mp2an
    opabbii
    eqtri
    eqer
end
