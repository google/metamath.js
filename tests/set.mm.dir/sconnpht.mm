include "csconn.mm"
include "wcel.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "cc0.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "wbr.mm"
include "cpconn.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "issconn.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "id.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "simplbiim.mm"
include "3imp.mm"

theorem sconnpht
  let cF: class F
  let cJ: class J
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. SConn /\ F e. ( II Cn J ) /\ ( F ` 0 ) = ( F ` 1 ) ) -> F ( ~=ph ` J ) ( ( 0 [,] 1 ) X. { ( F ` 0 ) } ) )

  proof
    cJ
    csconn
    wcel
    #
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cc0
    cF
    cfv
    #
    c1
    cF
    cfv
    #
    wceq
    #
    cF
    cc0
    c1
    cicc
    co
    #
    @3
    csn
    #
    cxp
    #
    cJ
    cphtpc
    cfv
    #
    wbr
    #
    @0
    cJ
    cpconn
    wcel
    cc0
    vf
    cv
    #
    cfv
    #
    c1
    @11
    cfv
    #
    wceq
    #
    @11
    @6
    @12
    csn
    #
    cxp
    #
    @9
    wbr
    #
    wi
    #
    vf
    @1
    wral
    @2
    @5
    @10
    wi
    #
    wi
    vf
    cJ
    issconn
    @18
    @19
    vf
    cF
    @1
    @11
    cF
    wceq
    #
    @14
    @5
    @17
    @10
    @20
    @12
    @3
    @13
    @4
    cc0
    @11
    cF
    fveq1
    #
    c1
    @11
    cF
    fveq1
    eqeq12d
    @20
    @11
    cF
    @16
    @8
    @9
    @20
    id
    @20
    @15
    @7
    @6
    @20
    @12
    @3
    @21
    sneqd
    xpeq2d
    breq12d
    imbi12d
    rspccv
    simplbiim
    3imp
end
