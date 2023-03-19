include "wcel.mm"
include "co.mm"
include "wo.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "isirred2.mm"
include "simp3bi.mm"
include "eqid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eleq1.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "orbi2d.mm"
include "rspc2v.mm"
include "mpii.mm"
include "syl5.mm"
include "3impia.mm"

theorem irredmul
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredmul.b: |- B = ( Base ` R )
  assume irredmul.u: |- U = ( Unit ` R )
  assume irredmul.t: |- .x. = ( .r ` R )


  assert |- ( ( X e. B /\ Y e. B /\ ( X .x. Y ) e. I ) -> ( X e. U \/ Y e. U ) )

  proof
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.x
    co
    #
    cI
    wcel
    #
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    wo
    #
    @3
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    @2
    wceq
    #
    @7
    cU
    wcel
    #
    @8
    cU
    wcel
    #
    wo
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @0
    @1
    wa
    #
    @6
    @3
    @2
    cB
    wcel
    @2
    cU
    wcel
    wn
    @15
    vx
    vy
    cB
    cR
    c.x
    cU
    cI
    @2
    irredmul.b
    irredmul.u
    irredn0.i
    irredmul.t
    isirred2
    simp3bi
    @16
    @15
    @2
    @2
    wceq
    #
    @6
    @2
    eqid
    @14
    @17
    @6
    wi
    cX
    @8
    c.x
    co
    #
    @2
    wceq
    #
    @4
    @12
    wo
    #
    wi
    vx
    vy
    cX
    cY
    cB
    cB
    @7
    cX
    wceq
    #
    @10
    @19
    @13
    @20
    @21
    @9
    @18
    @2
    @7
    cX
    @8
    c.x
    oveq1
    eqeq1d
    @21
    @11
    @4
    @12
    @7
    cX
    cU
    eleq1
    orbi1d
    imbi12d
    @8
    cY
    wceq
    #
    @19
    @17
    @20
    @6
    @22
    @18
    @2
    @2
    @8
    cY
    cX
    c.x
    oveq2
    eqeq1d
    @22
    @12
    @5
    @4
    @8
    cY
    cU
    eleq1
    orbi2d
    imbi12d
    rspc2v
    mpii
    syl5
    3impia
end
