include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "cui.mm"
include "cfv.mm"
include "wn.mm"
include "eqid.mm"
include "irrednu.mm"
include "wceq.mm"
include "1unit.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "syl5.mm"
include "imp.mm"

theorem irredn1
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.x: class .x.
  let cU: class U
  let cY: class Y
  let cB: class B
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredn1.o: |- .1. = ( 1r ` R )


  assert |- ( ( R e. Ring /\ X e. I ) -> X =/= .1. )

  proof
    cR
    crg
    wcel
    #
    cX
    cI
    wcel
    #
    cX
    c.1
    wne
    #
    @1
    cX
    cR
    cui
    cfv
    #
    wcel
    #
    wn
    @0
    @2
    cR
    @3
    cI
    cX
    irredn0.i
    @3
    eqid
    #
    irrednu
    @0
    @4
    cX
    c.1
    @0
    @4
    cX
    c.1
    wceq
    c.1
    @3
    wcel
    cR
    @3
    c.1
    @5
    irredn1.o
    1unit
    cX
    c.1
    @3
    eleq1
    syl5ibrcom
    necon3bd
    syl5
    imp
end
