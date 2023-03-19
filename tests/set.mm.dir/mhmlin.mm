include "cmhm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cbs.mm"
include "wf.mm"
include "c0g.mm"
include "cmnd.mm"
include "w3a.mm"
include "eqid.mm"
include "ismhm.mm"
include "simprbi.mm"
include "simp2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem mhmlin
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume mhmlin.b: |- B = ( Base ` S )
  assume mhmlin.p: |- .+ = ( +g ` S )
  assume mhmlin.q: |- .+^ = ( +g ` T )


  assert |- ( ( F e. ( S MndHom T ) /\ X e. B /\ Y e. B ) -> ( F ` ( X .+ Y ) ) = ( ( F ` X ) .+^ ( F ` Y ) ) )

  proof
    cF
    cS
    cT
    cmhm
    co
    wcel
    #
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
    c.pl
    co
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    @2
    wa
    @8
    @0
    cB
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @17
    cS
    c0g
    cfv
    #
    cF
    cfv
    cT
    c0g
    cfv
    #
    wceq
    #
    @0
    cS
    cmnd
    wcel
    cT
    cmnd
    wcel
    wa
    @19
    @17
    @22
    w3a
    vx
    vy
    cB
    @18
    c.pl
    c.pd
    cS
    cT
    cF
    @21
    @20
    mhmlin.b
    @18
    eqid
    mhmlin.p
    mhmlin.q
    @20
    eqid
    @21
    eqid
    ismhm
    simprbi
    simp2d
    @16
    @8
    cX
    @10
    c.pl
    co
    #
    cF
    cfv
    #
    @5
    @14
    c.pd
    co
    #
    wceq
    vx
    vy
    cX
    cY
    cB
    cB
    @9
    cX
    wceq
    #
    @12
    @24
    @15
    @25
    @26
    @11
    @23
    cF
    @9
    cX
    @10
    c.pl
    oveq1
    fveq2d
    @26
    @13
    @5
    @14
    c.pd
    @9
    cX
    cF
    fveq2
    oveq1d
    eqeq12d
    @10
    cY
    wceq
    #
    @24
    @4
    @25
    @7
    @27
    @23
    @3
    cF
    @10
    cY
    cX
    c.pl
    oveq2
    fveq2d
    @27
    @14
    @6
    @5
    c.pd
    @10
    cY
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    syl5com
    3impib
end
