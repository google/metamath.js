include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cres.mm"
include "cplusf.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "resmpt2.mm"
include "mp2an.mm"
include "wfn.mm"
include "fnov.mm"
include "mpbi.mm"
include "reseq1i.mm"
include "cbs.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cplusg.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssexi.mm"
include "eqid.mm"
include "ressplusg.mm"
include "eqtri.mm"
include "plusffval.mm"
include "3eqtr4ri.mm"

theorem ressplusf
  let cA: class A
  let cB: class B
  let c.pd: class .+^
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume ressplusf.1: |- B = ( Base ` G )
  assume ressplusf.2: |- H = ( G |`s A )
  assume ressplusf.3: |- .+^ = ( +g ` G )
  assume ressplusf.4: |- .+^ Fn ( B X. B )
  assume ressplusf.5: |- A C_ B


  assert |- ( +f ` H ) = ( .+^ |` ( A X. A ) )

  proof
    vx
    vy
    cB
    cB
    vx
    cv
    vy
    cv
    c.pd
    co
    #
    cmpt2
    #
    cA
    cA
    cxp
    #
    cres
    #
    vx
    vy
    cA
    cA
    @0
    cmpt2
    #
    c.pd
    @2
    cres
    cH
    cplusf
    cfv
    #
    cA
    cB
    wss
    #
    @6
    @3
    @4
    wceq
    ressplusf.5
    ressplusf.5
    vx
    vy
    cB
    cB
    cA
    cA
    @0
    resmpt2
    mp2an
    c.pd
    @1
    @2
    c.pd
    cB
    cB
    cxp
    wfn
    c.pd
    @1
    wceq
    ressplusf.4
    vx
    vy
    cB
    cB
    c.pd
    fnov
    mpbi
    reseq1i
    vx
    vy
    cA
    c.pd
    @5
    cH
    @6
    cA
    cH
    cbs
    cfv
    wceq
    ressplusf.5
    cA
    cB
    cH
    cG
    ressplusf.2
    ressplusf.1
    ressbas2
    ax-mp
    c.pd
    cG
    cplusg
    cfv
    #
    cH
    cplusg
    cfv
    #
    ressplusf.3
    cA
    cvv
    wcel
    @7
    @8
    wceq
    cA
    cB
    cB
    cG
    cbs
    cfv
    cvv
    ressplusf.1
    cG
    cbs
    fvex
    eqeltri
    ressplusf.5
    ssexi
    cA
    @7
    cG
    cH
    cvv
    ressplusf.2
    @7
    eqid
    ressplusg
    ax-mp
    eqtri
    @5
    eqid
    plusffval
    3eqtr4ri
end
