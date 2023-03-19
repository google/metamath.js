include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "simp1.mm"
include "cdm.mm"
include "clatglbcl2.mm"
include "3adant3.mm"
include "simp3.mm"
include "glble.mm"

theorem clatglble
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume clatglb.b: |- B = ( Base ` K )
  assume clatglb.l: |- .<_ = ( le ` K )
  assume clatglb.g: |- G = ( glb ` K )


  assert |- ( ( K e. CLat /\ S C_ B /\ X e. S ) -> ( G ` S ) .<_ X )

  proof
    cK
    ccla
    wcel
    #
    cS
    cB
    wss
    #
    cX
    cS
    wcel
    #
    w3a
    cB
    cS
    cG
    cK
    c.le
    ccla
    cX
    clatglb.b
    clatglb.l
    clatglb.g
    @0
    @1
    @2
    simp1
    @0
    @1
    cS
    cG
    cdm
    wcel
    @2
    cB
    cS
    cG
    cK
    clatglb.b
    clatglb.g
    clatglbcl2
    3adant3
    @0
    @1
    @2
    simp3
    glble
end
