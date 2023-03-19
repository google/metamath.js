include "chil.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cva.mm"
include "cno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "wi.mm"
include "c0v.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ifhvhv0.mm"
include "normpythi.mm"
include "dedth2h.mm"

theorem normpyth
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A .ih B ) = 0 -> ( ( normh ` ( A +h B ) ) ^ 2 ) = ( ( ( normh ` A ) ^ 2 ) + ( ( normh ` B ) ^ 2 ) ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cB
    csp
    co
    #
    cc0
    wceq
    #
    cA
    cB
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cno
    cfv
    #
    c2
    cexp
    co
    #
    cB
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    wi
    @0
    cA
    c0v
    cif
    #
    cB
    csp
    co
    #
    cc0
    wceq
    #
    @13
    cB
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @13
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @10
    caddc
    co
    #
    wceq
    #
    wi
    @13
    @1
    cB
    c0v
    cif
    #
    csp
    co
    #
    cc0
    wceq
    #
    @13
    @23
    cva
    co
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @20
    @23
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    wi
    cA
    cB
    c0v
    c0v
    cA
    @13
    wceq
    #
    @3
    @15
    @12
    @22
    @33
    @2
    @14
    cc0
    cA
    @13
    cB
    csp
    oveq1
    eqeq1d
    @33
    @6
    @18
    @11
    @21
    @33
    @5
    @17
    c2
    cexp
    @33
    @4
    @16
    cno
    cA
    @13
    cB
    cva
    oveq1
    fveq2d
    oveq1d
    @33
    @8
    @20
    @10
    caddc
    @33
    @7
    @19
    c2
    cexp
    cA
    @13
    cno
    fveq2
    oveq1d
    oveq1d
    eqeq12d
    imbi12d
    cB
    @23
    wceq
    #
    @15
    @25
    @22
    @32
    @34
    @14
    @24
    cc0
    cB
    @23
    @13
    csp
    oveq2
    eqeq1d
    @34
    @18
    @28
    @21
    @31
    @34
    @17
    @27
    c2
    cexp
    @34
    @16
    @26
    cno
    cB
    @23
    @13
    cva
    oveq2
    fveq2d
    oveq1d
    @34
    @10
    @30
    @20
    caddc
    @34
    @9
    @29
    c2
    cexp
    cB
    @23
    cno
    fveq2
    oveq1d
    oveq2d
    eqeq12d
    imbi12d
    @13
    @23
    cA
    ifhvhv0
    cB
    ifhvhv0
    normpythi
    dedth2h
end
