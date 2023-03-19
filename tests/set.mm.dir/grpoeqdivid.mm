include "cgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "co.mm"
include "grpodivid.mm"
include "3adant2.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "grponpcan.mm"
include "grpolid.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "impbid.mm"

theorem grpoeqdivid
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let cG: class G
  let cX: class X
  assume grpeqdivid.1: |- X = ran G
  assume grpeqdivid.2: |- U = ( GId ` G )
  assume grpeqdivid.3: |- D = ( /g ` G )


  assert |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) -> ( A = B <-> ( A D B ) = U ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    wceq
    #
    cA
    cB
    cD
    co
    #
    cU
    wceq
    #
    @3
    @6
    @4
    cB
    cB
    cD
    co
    #
    cU
    wceq
    #
    @0
    @2
    @8
    @1
    cB
    cD
    cU
    cG
    cX
    grpeqdivid.1
    grpeqdivid.3
    grpeqdivid.2
    grpodivid
    3adant2
    @4
    @5
    @7
    cU
    cA
    cB
    cB
    cD
    oveq1
    eqeq1d
    syl5ibrcom
    @6
    @5
    cB
    cG
    co
    #
    cU
    cB
    cG
    co
    #
    wceq
    @3
    @4
    @5
    cU
    cB
    cG
    oveq1
    @3
    @9
    cA
    @10
    cB
    cA
    cB
    cD
    cG
    cX
    grpeqdivid.1
    grpeqdivid.3
    grponpcan
    @0
    @2
    @10
    cB
    wceq
    @1
    cB
    cU
    cG
    cX
    grpeqdivid.1
    grpeqdivid.2
    grpolid
    3adant2
    eqeq12d
    syl5ib
    impbid
end
