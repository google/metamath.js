include "cnpi.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmi.mm"
include "co.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpq.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "oveq2d.mm"
include "df-mpq.mm"
include "opex.mm"
include "ovmpt2.mm"

theorem mulpipq2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( A e. ( N. X. N. ) /\ B e. ( N. X. N. ) ) -> ( A .pQ B ) = <. ( ( 1st ` A ) .N ( 1st ` B ) ) , ( ( 2nd ` A ) .N ( 2nd ` B ) ) >. )

  proof
    vx
    vy
    cA
    cB
    cnpi
    cnpi
    cxp
    #
    @0
    vx
    cv
    #
    c1st
    cfv
    #
    vy
    cv
    #
    c1st
    cfv
    #
    cmi
    co
    #
    @1
    c2nd
    cfv
    #
    @3
    c2nd
    cfv
    #
    cmi
    co
    #
    cop
    cA
    c1st
    cfv
    #
    cB
    c1st
    cfv
    #
    cmi
    co
    #
    cA
    c2nd
    cfv
    #
    cB
    c2nd
    cfv
    #
    cmi
    co
    #
    cop
    cmpq
    @9
    @4
    cmi
    co
    #
    @12
    @7
    cmi
    co
    #
    cop
    @1
    cA
    wceq
    #
    @5
    @15
    @8
    @16
    @17
    @2
    @9
    @4
    cmi
    @1
    cA
    c1st
    fveq2
    oveq1d
    @17
    @6
    @12
    @7
    cmi
    @1
    cA
    c2nd
    fveq2
    oveq1d
    opeq12d
    @3
    cB
    wceq
    #
    @15
    @11
    @16
    @14
    @18
    @4
    @10
    @9
    cmi
    @3
    cB
    c1st
    fveq2
    oveq2d
    @18
    @7
    @13
    @12
    cmi
    @3
    cB
    c2nd
    fveq2
    oveq2d
    opeq12d
    vx
    vy
    df-mpq
    @11
    @14
    opex
    ovmpt2
end
