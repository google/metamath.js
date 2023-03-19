include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cioc.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cif.mm"
include "exmid.mm"
include "cle.mm"
include "xrltle.mm"
include "imp.mm"
include "3adantl3.mm"
include "iocinioc2.mm"
include "syldan.mm"
include "ex.mm"
include "ancld.mm"
include "simpl2.mm"
include "simpl1.mm"
include "simpr.mm"
include "xrlenlt.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "3ancoma.mm"
include "incom.mm"
include "syl5eqr.mm"
include "sylanbr.mm"
include "orim12d.mm"
include "mpi.mm"
include "eqif.mm"
include "sylibr.mm"

theorem iocinif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( A (,] C ) i^i ( B (,] C ) ) = if ( A < B , ( B (,] C ) , ( A (,] C ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cC
    cioc
    co
    #
    cB
    cC
    cioc
    co
    #
    cin
    #
    @6
    wceq
    #
    wa
    #
    @4
    wn
    #
    @7
    @5
    wceq
    #
    wa
    #
    wo
    #
    @7
    @4
    @6
    @5
    cif
    wceq
    @3
    @4
    @10
    wo
    @13
    @4
    exmid
    @3
    @4
    @9
    @10
    @12
    @3
    @4
    @8
    @3
    @4
    @8
    @3
    @4
    cA
    cB
    cle
    wbr
    #
    @8
    @0
    @1
    @4
    @14
    @2
    @0
    @1
    wa
    @4
    @14
    cA
    cB
    xrltle
    imp
    3adantl3
    cA
    cB
    cC
    iocinioc2
    syldan
    ex
    ancld
    @3
    @10
    @11
    @3
    @10
    @11
    @3
    @10
    cB
    cA
    cle
    wbr
    #
    @11
    @3
    @10
    wa
    @1
    @0
    @10
    @15
    @0
    @1
    @2
    @10
    simpl2
    @0
    @1
    @2
    @10
    simpl1
    @3
    @10
    simpr
    @1
    @0
    wa
    @15
    @10
    cB
    cA
    xrlenlt
    biimpar
    syl21anc
    @3
    @1
    @0
    @2
    w3a
    #
    @15
    @11
    @1
    @0
    @2
    3ancoma
    @16
    @15
    wa
    @7
    @6
    @5
    cin
    @5
    @6
    @5
    incom
    cB
    cA
    cC
    iocinioc2
    syl5eqr
    sylanbr
    syldan
    ex
    ancld
    orim12d
    mpi
    @4
    @7
    @6
    @5
    eqif
    sylibr
end
