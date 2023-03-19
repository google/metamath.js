include "cablo.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cgi.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "id.mm"
include "3anidm12.mm"
include "ablodivdiv.mm"
include "sylan2.mm"
include "3impb.mm"
include "cgr.mm"
include "ablogrpo.mm"
include "eqid.mm"
include "grpodivid.mm"
include "sylan.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "grpolid.mm"
include "3adant2.mm"
include "3eqtrd.mm"

theorem ablonncan
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cX: class X
  assume abldiv.1: |- X = ran G
  assume abldiv.3: |- D = ( /g ` G )


  assert |- ( ( G e. AbelOp /\ A e. X /\ B e. X ) -> ( A D ( A D B ) ) = B )

  proof
    cG
    cablo
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
    cA
    cB
    cD
    co
    cD
    co
    #
    cA
    cA
    cD
    co
    #
    cB
    cG
    co
    #
    cG
    cgi
    cfv
    #
    cB
    cG
    co
    #
    cB
    @0
    @1
    @2
    @4
    @6
    wceq
    #
    @1
    @2
    wa
    @0
    @1
    @1
    @2
    w3a
    #
    @9
    @1
    @2
    @10
    @10
    id
    3anidm12
    cA
    cA
    cB
    cD
    cG
    cX
    abldiv.1
    abldiv.3
    ablodivdiv
    sylan2
    3impb
    @3
    @5
    @7
    cB
    cG
    @0
    @1
    @5
    @7
    wceq
    #
    @2
    @0
    cG
    cgr
    wcel
    #
    @1
    @11
    cG
    ablogrpo
    #
    cA
    cD
    @7
    cG
    cX
    abldiv.1
    abldiv.3
    @7
    eqid
    #
    grpodivid
    sylan
    3adant3
    oveq1d
    @0
    @2
    @8
    cB
    wceq
    #
    @1
    @0
    @12
    @2
    @15
    @13
    cB
    @7
    cG
    cX
    abldiv.1
    @14
    grpolid
    sylan
    3adant2
    3eqtrd
end
