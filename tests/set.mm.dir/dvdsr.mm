include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wrel.mm"
include "reldvdsr.mm"
include "brrelex12.mm"
include "mpan.mm"
include "elex.mm"
include "id.mm"
include "ovex.mm"
include "syl6eqelr.mm"
include "rexlimivw.mm"
include "anim12i.mm"
include "simpl.mm"
include "eleq1d.mm"
include "oveq2d.mm"
include "simpr.mm"
include "eqeq12d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "dvdsrval.mm"
include "brabga.mm"
include "pm5.21nii.mm"

theorem dvdsr
  let vz: setvar z
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let cZ: class Z
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )
  assume dvdsr.3: |- .x. = ( .r ` R )

  disjoint B z
  disjoint X z
  disjoint Y z
  disjoint R z
  disjoint .x. z
  disjoint x y
  disjoint .|| x
  disjoint .|| y
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B r
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint Z x
  disjoint Z y
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint .x. r
  disjoint .x. x
  disjoint .x. y
  assert |- ( X .|| Y <-> ( X e. B /\ E. z e. B ( z .x. X ) = Y ) )

  proof
    cX
    cY
    c.pa
    wbr
    #
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    vz
    cv
    #
    cX
    c.x
    co
    #
    cY
    wceq
    #
    vz
    cB
    wrex
    #
    wa
    #
    c.pa
    wrel
    @0
    @3
    c.pa
    cR
    dvdsr.2
    reldvdsr
    cX
    cY
    c.pa
    brrelex12
    mpan
    @4
    @1
    @8
    @2
    cX
    cB
    elex
    @7
    @2
    vz
    cB
    @7
    cY
    @6
    cvv
    @7
    id
    @5
    cX
    c.x
    ovex
    syl6eqelr
    rexlimivw
    anim12i
    vx
    cv
    #
    cB
    wcel
    #
    @5
    @10
    c.x
    co
    #
    vy
    cv
    #
    wceq
    #
    vz
    cB
    wrex
    #
    wa
    @9
    vx
    vy
    cX
    cY
    c.pa
    cvv
    cvv
    @10
    cX
    wceq
    #
    @13
    cY
    wceq
    #
    wa
    #
    @11
    @4
    @15
    @8
    @18
    @10
    cX
    cB
    @16
    @17
    simpl
    #
    eleq1d
    @18
    @14
    @7
    vz
    cB
    @18
    @12
    @6
    @13
    cY
    @18
    @10
    cX
    @5
    c.x
    @19
    oveq2d
    @16
    @17
    simpr
    eqeq12d
    rexbidv
    anbi12d
    vx
    vy
    vz
    cB
    c.pa
    cR
    c.x
    dvdsr.1
    dvdsr.2
    dvdsr.3
    dvdsrval
    brabga
    pm5.21nii
end
