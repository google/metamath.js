include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "cfv.mm"
include "wa.mm"
include "cui.mm"
include "eqid.mm"
include "drngunit.mm"
include "crg.mm"
include "wi.mm"
include "drngring.mm"
include "ringinvcl.mm"
include "ex.mm"
include "syl.mm"
include "sylbird.mm"
include "3impib.mm"

theorem drnginvrcl
  let cB: class B
  let cR: class R
  let cI: class I
  let cX: class X
  let c.0: class .0.
  assume invrcl.b: |- B = ( Base ` R )
  assume invrcl.z: |- .0. = ( 0g ` R )
  assume invrcl.i: |- I = ( invr ` R )


  assert |- ( ( R e. DivRing /\ X e. B /\ X =/= .0. ) -> ( I ` X ) e. B )

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
    cI
    cfv
    cB
    wcel
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
    invrcl.b
    @4
    eqid
    #
    invrcl.z
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
    cB
    cR
    @4
    cI
    cX
    @6
    invrcl.i
    invrcl.b
    ringinvcl
    ex
    syl
    sylbird
    3impib
end
