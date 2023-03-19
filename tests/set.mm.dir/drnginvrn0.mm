include "cdr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "cui.mm"
include "crg.mm"
include "wi.mm"
include "drngring.mm"
include "eqid.mm"
include "unitinvcl.mm"
include "ex.mm"
include "syl.mm"
include "drngunit.mm"
include "3imtr3d.mm"
include "3impib.mm"
include "simprd.mm"

theorem drnginvrn0
  let cB: class B
  let cR: class R
  let cI: class I
  let cX: class X
  let c.0: class .0.
  assume invrcl.b: |- B = ( Base ` R )
  assume invrcl.z: |- .0. = ( 0g ` R )
  assume invrcl.i: |- I = ( invr ` R )


  assert |- ( ( R e. DivRing /\ X e. B /\ X =/= .0. ) -> ( I ` X ) =/= .0. )

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
    w3a
    cX
    cI
    cfv
    #
    cB
    wcel
    #
    @3
    c.0
    wne
    #
    @0
    @1
    @2
    @4
    @5
    wa
    #
    @0
    cX
    cR
    cui
    cfv
    #
    wcel
    #
    @3
    @7
    wcel
    #
    @1
    @2
    wa
    @6
    @0
    cR
    crg
    wcel
    #
    @8
    @9
    wi
    cR
    drngring
    @10
    @8
    @9
    cR
    @7
    cI
    cX
    @7
    eqid
    #
    invrcl.i
    unitinvcl
    ex
    syl
    cB
    cR
    @7
    cX
    c.0
    invrcl.b
    @11
    invrcl.z
    drngunit
    cB
    cR
    @7
    @3
    c.0
    invrcl.b
    @11
    invrcl.z
    drngunit
    3imtr3d
    3impib
    simprd
end
