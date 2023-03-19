include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "iitopon.mm"
include "cnconst2.mm"
include "mp3an1.mm"
include "syl5eqel.mm"
include "fveq1i.mm"
include "simpr.mm"
include "0elunit.mm"
include "fvconst2g.mm"
include "sylancl.mm"
include "syl5eq.mm"
include "1elunit.mm"
include "3jca.mm"

theorem pcoptcl
  let cP: class P
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assume pcopt.1: |- P = ( ( 0 [,] 1 ) X. { Y } )


  assert |- ( ( J e. ( TopOn ` X ) /\ Y e. X ) -> ( P e. ( II Cn J ) /\ ( P ` 0 ) = Y /\ ( P ` 1 ) = Y ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cY
    cX
    wcel
    #
    wa
    #
    cP
    cii
    cJ
    ccn
    co
    #
    wcel
    cc0
    cP
    cfv
    #
    cY
    wceq
    c1
    cP
    cfv
    #
    cY
    wceq
    @2
    cP
    cc0
    c1
    cicc
    co
    #
    cY
    csn
    cxp
    #
    @3
    pcopt.1
    cii
    @6
    ctopon
    cfv
    wcel
    @0
    @1
    @7
    @3
    wcel
    iitopon
    cY
    cii
    cJ
    @6
    cX
    cnconst2
    mp3an1
    syl5eqel
    @2
    @4
    cc0
    @7
    cfv
    #
    cY
    cc0
    cP
    @7
    pcopt.1
    fveq1i
    @2
    @1
    cc0
    @6
    wcel
    @8
    cY
    wceq
    @0
    @1
    simpr
    #
    0elunit
    @6
    cY
    cc0
    cX
    fvconst2g
    sylancl
    syl5eq
    @2
    @5
    c1
    @7
    cfv
    #
    cY
    c1
    cP
    @7
    pcopt.1
    fveq1i
    @2
    @1
    c1
    @6
    wcel
    @10
    cY
    wceq
    @9
    1elunit
    @6
    cY
    c1
    cX
    fvconst2g
    sylancl
    syl5eq
    3jca
end
