include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "simp1.mm"
include "sstr2.mm"
include "impcom.mm"
include "3adant1.mm"
include "clatlubcl.mm"
include "3adant3.mm"
include "3jca.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "ssel2.mm"
include "3ad2antl3.mm"
include "lubub.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "lubl.mm"
include "sylc.mm"

theorem lubss
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let vz: setvar z
  let vy: setvar y
  let cX: class X
  assume lublem.b: |- B = ( Base ` K )
  assume lublem.l: |- .<_ = ( le ` K )
  assume lublem.u: |- U = ( lub ` K )


  assert |- ( ( K e. CLat /\ T C_ B /\ S C_ T ) -> ( U ` S ) .<_ ( U ` T ) )

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
    @0
    cS
    cB
    wss
    #
    cT
    cU
    cfv
    #
    cB
    wcel
    #
    w3a
    vy
    cv
    #
    @5
    c.le
    wbr
    #
    vy
    cS
    wral
    cS
    cU
    cfv
    @5
    c.le
    wbr
    @3
    @0
    @4
    @6
    @0
    @1
    @2
    simp1
    @1
    @2
    @4
    @0
    @2
    @1
    @4
    cS
    cT
    cB
    sstr2
    impcom
    3adant1
    @0
    @1
    @6
    @2
    cB
    cT
    cU
    cK
    lublem.b
    lublem.u
    clatlubcl
    3adant3
    3jca
    @3
    @8
    vy
    cS
    @3
    @7
    cS
    wcel
    #
    wa
    @0
    @1
    @7
    cT
    wcel
    #
    @8
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
    @2
    @0
    @9
    @10
    @1
    cS
    cT
    @7
    ssel2
    3ad2antl3
    cB
    cT
    cU
    cK
    c.le
    @7
    lublem.b
    lublem.l
    lublem.u
    lubub
    syl3anc
    ralrimiva
    vy
    cB
    cS
    cU
    cK
    c.le
    @5
    lublem.b
    lublem.l
    lublem.u
    lubl
    sylc
end
