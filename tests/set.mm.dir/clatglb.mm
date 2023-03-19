include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "simpl.mm"
include "clatglbcl2.mm"
include "glbprop.mm"

theorem clatglb
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let c.le: class .<_
  assume clatglb.b: |- B = ( Base ` K )
  assume clatglb.l: |- .<_ = ( le ` K )
  assume clatglb.g: |- G = ( glb ` K )

  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint K y
  disjoint K z
  disjoint .<_ y
  disjoint .<_ z
  disjoint S y
  disjoint S z
  assert |- ( ( K e. CLat /\ S C_ B ) -> ( A. y e. S ( G ` S ) .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ ( G ` S ) ) ) )

  proof
    cK
    ccla
    wcel
    #
    cS
    cB
    wss
    #
    wa
    vy
    vz
    cB
    cS
    cG
    cK
    c.le
    ccla
    clatglb.b
    clatglb.l
    clatglb.g
    @0
    @1
    simpl
    cB
    cS
    cG
    cK
    clatglb.b
    clatglb.g
    clatglbcl2
    glbprop
end
