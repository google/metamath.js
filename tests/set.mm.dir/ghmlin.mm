include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cbs.mm"
include "wf.mm"
include "cgrp.mm"
include "eqid.mm"
include "isghm.mm"
include "simprbi.mm"
include "simprd.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "3impb.mm"

theorem ghmlin
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume ghmlin.x: |- X = ( Base ` S )
  assume ghmlin.a: |- .+ = ( +g ` S )
  assume ghmlin.b: |- .+^ = ( +g ` T )


  assert |- ( ( F e. ( S GrpHom T ) /\ U e. X /\ V e. X ) -> ( F ` ( U .+ V ) ) = ( ( F ` U ) .+^ ( F ` V ) ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cU
    cX
    wcel
    #
    cV
    cX
    wcel
    #
    cU
    cV
    c.pl
    co
    #
    cF
    cfv
    #
    cU
    cF
    cfv
    #
    cV
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    @0
    va
    cv
    #
    vb
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
    vb
    cX
    wral
    va
    cX
    wral
    #
    @1
    @2
    wa
    @8
    @0
    cX
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @17
    @0
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    wa
    @19
    @17
    wa
    vb
    va
    c.pl
    c.pd
    cS
    cT
    cF
    cX
    @18
    ghmlin.x
    @18
    eqid
    ghmlin.a
    ghmlin.b
    isghm
    simprbi
    simprd
    @16
    @8
    cU
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
    va
    vb
    cU
    cV
    cX
    cX
    @9
    cU
    wceq
    #
    @12
    @21
    @15
    @22
    @23
    @11
    @20
    cF
    @9
    cU
    @10
    c.pl
    oveq1
    fveq2d
    @23
    @13
    @5
    @14
    c.pd
    @9
    cU
    cF
    fveq2
    oveq1d
    eqeq12d
    @10
    cV
    wceq
    #
    @21
    @4
    @22
    @7
    @24
    @20
    @3
    cF
    @10
    cV
    cU
    c.pl
    oveq2
    fveq2d
    @24
    @14
    @6
    @5
    c.pd
    @10
    cV
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    mpan9
    3impb
end
