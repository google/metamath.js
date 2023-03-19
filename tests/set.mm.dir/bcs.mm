include "chil.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cno.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "c0v.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ifhvhv0.mm"
include "bcsiHIL.mm"
include "dedth2h.mm"

theorem bcs
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( abs ` ( A .ih B ) ) <_ ( ( normh ` A ) x. ( normh ` B ) ) )

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
    cabs
    cfv
    #
    cA
    cno
    cfv
    #
    cB
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    @0
    cA
    c0v
    cif
    #
    cB
    csp
    co
    #
    cabs
    cfv
    #
    @7
    cno
    cfv
    #
    @5
    cmul
    co
    #
    cle
    wbr
    @7
    @1
    cB
    c0v
    cif
    #
    csp
    co
    #
    cabs
    cfv
    #
    @10
    @12
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    cA
    cB
    c0v
    c0v
    cA
    @7
    wceq
    #
    @3
    @9
    @6
    @11
    cle
    @17
    @2
    @8
    cabs
    cA
    @7
    cB
    csp
    oveq1
    fveq2d
    @17
    @4
    @10
    @5
    cmul
    cA
    @7
    cno
    fveq2
    oveq1d
    breq12d
    cB
    @12
    wceq
    #
    @9
    @14
    @11
    @16
    cle
    @18
    @8
    @13
    cabs
    cB
    @12
    @7
    csp
    oveq2
    fveq2d
    @18
    @5
    @15
    @10
    cmul
    cB
    @12
    cno
    fveq2
    oveq2d
    breq12d
    @7
    @12
    cA
    ifhvhv0
    cB
    ifhvhv0
    bcsiHIL
    dedth2h
end
