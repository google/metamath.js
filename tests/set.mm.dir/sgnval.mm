include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cneg.mm"
include "cif.mm"
include "cxr.mm"
include "csgn.mm"
include "eqeq1.mm"
include "breq1.mm"
include "ifbid.mm"
include "ifbieq2d.mm"
include "df-sgn.mm"
include "c0ex.mm"
include "negex.mm"
include "1ex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem sgnval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. RR* -> ( sgn ` A ) = if ( A = 0 , 0 , if ( A < 0 , -u 1 , 1 ) ) )

  proof
    vx
    cA
    vx
    cv
    #
    cc0
    wceq
    #
    cc0
    @0
    cc0
    clt
    wbr
    #
    c1
    cneg
    #
    c1
    cif
    #
    cif
    cA
    cc0
    wceq
    #
    cc0
    cA
    cc0
    clt
    wbr
    #
    @3
    c1
    cif
    #
    cif
    cxr
    csgn
    @0
    cA
    wceq
    #
    @1
    @5
    @4
    @7
    cc0
    @0
    cA
    cc0
    eqeq1
    @8
    @2
    @6
    @3
    c1
    @0
    cA
    cc0
    clt
    breq1
    ifbid
    ifbieq2d
    vx
    df-sgn
    @5
    cc0
    @7
    c0ex
    @6
    @3
    c1
    c1
    negex
    1ex
    ifex
    ifex
    fvmpt
end
