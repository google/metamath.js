include "cnpi.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmi.mm"
include "co.mm"
include "cpli.mm"
include "cop.mm"
include "cplpq.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "df-plpq.mm"
include "opex.mm"
include "ovmpt2.mm"

theorem addpipq2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( ( A e. ( N. X. N. ) /\ B e. ( N. X. N. ) ) -> ( A +pQ B ) = <. ( ( ( 1st ` A ) .N ( 2nd ` B ) ) +N ( ( 1st ` B ) .N ( 2nd ` A ) ) ) , ( ( 2nd ` A ) .N ( 2nd ` B ) ) >. )

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
    c2nd
    cfv
    #
    cmi
    co
    #
    @3
    c1st
    cfv
    #
    @1
    c2nd
    cfv
    #
    cmi
    co
    #
    cpli
    co
    #
    @7
    @4
    cmi
    co
    #
    cop
    cA
    c1st
    cfv
    #
    cB
    c2nd
    cfv
    #
    cmi
    co
    #
    cB
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cmi
    co
    #
    cpli
    co
    #
    @15
    @12
    cmi
    co
    #
    cop
    cplpq
    @11
    @4
    cmi
    co
    #
    @6
    @15
    cmi
    co
    #
    cpli
    co
    #
    @15
    @4
    cmi
    co
    #
    cop
    @1
    cA
    wceq
    #
    @9
    @21
    @10
    @22
    @23
    @5
    @19
    @8
    @20
    cpli
    @23
    @2
    @11
    @4
    cmi
    @1
    cA
    c1st
    fveq2
    oveq1d
    @23
    @7
    @15
    @6
    cmi
    @1
    cA
    c2nd
    fveq2
    #
    oveq2d
    oveq12d
    @23
    @7
    @15
    @4
    cmi
    @24
    oveq1d
    opeq12d
    @3
    cB
    wceq
    #
    @21
    @17
    @22
    @18
    @25
    @19
    @13
    @20
    @16
    cpli
    @25
    @4
    @12
    @11
    cmi
    @3
    cB
    c2nd
    fveq2
    #
    oveq2d
    @25
    @6
    @14
    @15
    cmi
    @3
    cB
    c1st
    fveq2
    oveq1d
    oveq12d
    @25
    @4
    @12
    @15
    cmi
    @26
    oveq2d
    opeq12d
    vx
    vy
    df-plpq
    @17
    @18
    opex
    ovmpt2
end
