include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cui.mm"
include "eqid.mm"
include "drngunit.mm"
include "crg.mm"
include "wi.mm"
include "drngring.mm"
include "unitrinv.mm"
include "ex.mm"
include "syl.mm"
include "sylbird.mm"
include "3impib.mm"

theorem drnginvrr
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cI: class I
  let cX: class X
  let c.0: class .0.
  assume drnginvrl.b: |- B = ( Base ` R )
  assume drnginvrl.z: |- .0. = ( 0g ` R )
  assume drnginvrl.t: |- .x. = ( .r ` R )
  assume drnginvrl.u: |- .1. = ( 1r ` R )
  assume drnginvrl.i: |- I = ( invr ` R )


  assert |- ( ( R e. DivRing /\ X e. B /\ X =/= .0. ) -> ( X .x. ( I ` X ) ) = .1. )

  proof
    cR
    cdr
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    cX
    cX
    cI
    cfv
    c.x
    co
    c.1
    wceq
    #
    @0
    @1
    @2
    wa
    cX
    cR
    cui
    cfv
    #
    wcel
    #
    @3
    cB
    cR
    @4
    cX
    c.0
    drnginvrl.b
    @4
    eqid
    #
    drnginvrl.z
    drngunit
    @0
    cR
    crg
    wcel
    #
    @5
    @3
    wi
    cR
    drngring
    @7
    @5
    @3
    cR
    c.x
    @4
    c.1
    cI
    cX
    @6
    drnginvrl.i
    drnginvrl.t
    drnginvrl.u
    unitrinv
    ex
    syl
    sylbird
    3impib
end
