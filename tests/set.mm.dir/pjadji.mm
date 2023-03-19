include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "c0v.mm"
include "cif.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ifhvhv0.mm"
include "pjadjii.mm"
include "dedth2h.mm"

theorem pjadji
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjadjt.1: |- H e. CH


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( ( projh ` H ) ` A ) .ih B ) = ( A .ih ( ( projh ` H ) ` B ) ) )

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
    cH
    cpjh
    cfv
    #
    cfv
    #
    cB
    csp
    co
    #
    cA
    cB
    @2
    cfv
    #
    csp
    co
    #
    wceq
    @0
    cA
    c0v
    cif
    #
    @2
    cfv
    #
    cB
    csp
    co
    #
    @7
    @5
    csp
    co
    #
    wceq
    @8
    @1
    cB
    c0v
    cif
    #
    csp
    co
    #
    @7
    @11
    @2
    cfv
    #
    csp
    co
    #
    wceq
    cA
    cB
    c0v
    c0v
    cA
    @7
    wceq
    #
    @4
    @9
    @6
    @10
    @15
    @3
    @8
    cB
    csp
    cA
    @7
    @2
    fveq2
    oveq1d
    cA
    @7
    @5
    csp
    oveq1
    eqeq12d
    cB
    @11
    wceq
    #
    @9
    @12
    @10
    @14
    cB
    @11
    @8
    csp
    oveq2
    @16
    @5
    @13
    @7
    csp
    cB
    @11
    @2
    fveq2
    oveq2d
    eqeq12d
    @7
    @11
    cH
    pjadjt.1
    cA
    ifhvhv0
    cB
    ifhvhv0
    pjadjii
    dedth2h
end
