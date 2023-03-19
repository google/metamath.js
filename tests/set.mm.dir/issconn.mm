include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cicc.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "wbr.mm"
include "wi.mm"
include "cii.mm"
include "ccn.mm"
include "wral.mm"
include "cpconn.mm"
include "csconn.mm"
include "oveq2.mm"
include "fveq2.mm"
include "breqd.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "df-sconn.mm"
include "elrab2.mm"

theorem issconn
  let vf: setvar f
  let cJ: class J
  let cF: class F
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y

  disjoint J f
  disjoint F f
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint x y
  disjoint J x
  disjoint J y
  assert |- ( J e. SConn <-> ( J e. PConn /\ A. f e. ( II Cn J ) ( ( f ` 0 ) = ( f ` 1 ) -> f ( ~=ph ` J ) ( ( 0 [,] 1 ) X. { ( f ` 0 ) } ) ) ) )

  proof
    cc0
    vf
    cv
    #
    cfv
    #
    c1
    @0
    cfv
    wceq
    #
    @0
    cc0
    c1
    cicc
    co
    @1
    csn
    cxp
    #
    vj
    cv
    #
    cphtpc
    cfv
    #
    wbr
    #
    wi
    #
    vf
    cii
    @4
    ccn
    co
    #
    wral
    @2
    @0
    @3
    cJ
    cphtpc
    cfv
    #
    wbr
    #
    wi
    #
    vf
    cii
    cJ
    ccn
    co
    #
    wral
    vj
    cJ
    cpconn
    csconn
    @4
    cJ
    wceq
    #
    @7
    @11
    vf
    @8
    @12
    @4
    cJ
    cii
    ccn
    oveq2
    @13
    @6
    @10
    @2
    @13
    @5
    @9
    @0
    @3
    @4
    cJ
    cphtpc
    fveq2
    breqd
    imbi2d
    raleqbidv
    vf
    vj
    df-sconn
    elrab2
end
