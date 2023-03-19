include "cmnd.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "mndplusf.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "c0g.mm"
include "simpr.mm"
include "eqid.mm"
include "mndidcl.mm"
include "adantr.mm"
include "mndrid.mm"
include "eqcomd.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "plusfval.mm"
include "eqeq2d.mm"
include "2rexbiia.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "foov.mm"
include "sylanbrc.mm"

theorem mndpfo
  let cB: class B
  let c.pd: class .+^
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mndpf.b: |- B = ( Base ` G )
  assume mndpf.p: |- .+^ = ( +f ` G )


  assert |- ( G e. Mnd -> .+^ : ( B X. B ) -onto-> B )

  proof
    cG
    cmnd
    wcel
    #
    cB
    cB
    cxp
    #
    cB
    c.pd
    wf
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    c.pd
    co
    #
    wceq
    #
    vz
    cB
    wrex
    vy
    cB
    wrex
    #
    vx
    cB
    wral
    @1
    cB
    c.pd
    wfo
    cB
    c.pd
    cG
    mndpf.b
    mndpf.p
    mndplusf
    @0
    @7
    vx
    cB
    @0
    @2
    cB
    wcel
    #
    wa
    #
    @2
    @3
    @4
    cG
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vz
    cB
    wrex
    vy
    cB
    wrex
    #
    @7
    @9
    @8
    cG
    c0g
    cfv
    #
    cB
    wcel
    #
    @2
    @2
    @14
    @10
    co
    #
    wceq
    @13
    @0
    @8
    simpr
    @0
    @15
    @8
    cB
    cG
    @14
    mndpf.b
    @14
    eqid
    #
    mndidcl
    adantr
    @9
    @16
    @2
    cB
    @10
    cG
    @2
    @14
    mndpf.b
    @10
    eqid
    #
    @17
    mndrid
    eqcomd
    vy
    vz
    cB
    cB
    @2
    @14
    @2
    @10
    rspceov
    syl3anc
    @6
    @12
    vy
    vz
    cB
    cB
    @3
    cB
    wcel
    @4
    cB
    wcel
    wa
    @5
    @11
    @2
    cB
    @10
    c.pd
    cG
    @3
    @4
    mndpf.b
    @18
    mndpf.p
    plusfval
    eqeq2d
    2rexbiia
    sylibr
    ralrimiva
    vy
    vz
    vx
    cB
    cB
    cB
    c.pd
    foov
    sylanbrc
end
