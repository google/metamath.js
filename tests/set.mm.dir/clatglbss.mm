include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simp3.mm"
include "sselda.mm"
include "clatglble.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simp1.mm"
include "clatglbcl.mm"
include "3adant3.mm"
include "sstr.mm"
include "ancoms.mm"
include "3adant1.mm"
include "clatleglb.mm"
include "mpbird.mm"

theorem clatglbss
  let cB: class B
  let cS: class S
  let cT: class T
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume clatglb.b: |- B = ( Base ` K )
  assume clatglb.l: |- .<_ = ( le ` K )
  assume clatglb.g: |- G = ( glb ` K )


  assert |- ( ( K e. CLat /\ T C_ B /\ S C_ T ) -> ( G ` T ) .<_ ( G ` S ) )

  proof
    cK
    ccla
    wcel
    #
    cT
    cB
    wss
    #
    cS
    cT
    wss
    #
    w3a
    #
    cT
    cG
    cfv
    #
    cS
    cG
    cfv
    c.le
    wbr
    #
    @4
    vy
    cv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @3
    @7
    vy
    cS
    @3
    @6
    cS
    wcel
    #
    wa
    @0
    @1
    @6
    cT
    wcel
    @7
    @0
    @1
    @2
    @9
    simpl1
    @0
    @1
    @2
    @9
    simpl2
    @3
    cS
    cT
    @6
    @0
    @1
    @2
    simp3
    sselda
    cB
    cT
    cG
    cK
    c.le
    @6
    clatglb.b
    clatglb.l
    clatglb.g
    clatglble
    syl3anc
    ralrimiva
    @3
    @0
    @4
    cB
    wcel
    #
    cS
    cB
    wss
    #
    @5
    @8
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @10
    @2
    cB
    cT
    cG
    cK
    clatglb.b
    clatglb.g
    clatglbcl
    3adant3
    @1
    @2
    @11
    @0
    @2
    @1
    @11
    cS
    cT
    cB
    sstr
    ancoms
    3adant1
    vy
    cB
    cS
    cG
    cK
    c.le
    @4
    clatglb.b
    clatglb.l
    clatglb.g
    clatleglb
    syl3anc
    mpbird
end
