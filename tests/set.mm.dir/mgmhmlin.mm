include "cmgmhm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cmgm.mm"
include "wa.mm"
include "cbs.mm"
include "wf.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "eqid.mm"
include "ismgmhm.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "com12.mm"
include "ad2antll.mm"
include "sylbi.mm"
include "3impib.mm"

theorem mgmhmlin
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
  let vk: setvar k
  assume mgmhmlin.b: |- B = ( Base ` S )
  assume mgmhmlin.p: |- .+ = ( +g ` S )
  assume mgmhmlin.q: |- .+^ = ( +g ` T )


  assert |- ( ( F e. ( S MgmHom T ) /\ X e. B /\ Y e. B ) -> ( F ` ( X .+ Y ) ) = ( ( F ` X ) .+^ ( F ` Y ) ) )

  proof
    cF
    cS
    cT
    cmgmhm
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
    cS
    cmgm
    wcel
    cT
    cmgm
    wcel
    wa
    #
    cB
    cT
    cbs
    cfv
    #
    cF
    wf
    #
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
    @12
    cF
    cfv
    #
    @13
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
    wa
    wa
    @1
    @2
    wa
    #
    @8
    wi
    #
    vx
    vy
    cB
    @10
    c.pl
    c.pd
    cS
    cT
    cF
    mgmhmlin.b
    @10
    eqid
    mgmhmlin.p
    mgmhmlin.q
    ismgmhm
    @20
    @22
    @9
    @11
    @21
    @20
    @8
    @19
    @8
    cX
    @13
    c.pl
    co
    #
    cF
    cfv
    #
    @5
    @17
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
    @12
    cX
    wceq
    #
    @15
    @24
    @18
    @25
    @26
    @14
    @23
    cF
    @12
    cX
    @13
    c.pl
    oveq1
    fveq2d
    @26
    @16
    @5
    @17
    c.pd
    @12
    cX
    cF
    fveq2
    oveq1d
    eqeq12d
    @13
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
    @13
    cY
    cX
    c.pl
    oveq2
    fveq2d
    @27
    @17
    @6
    @5
    c.pd
    @13
    cY
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    com12
    ad2antll
    sylbi
    3impib
end
