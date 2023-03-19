include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cxne.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "xnegcl.mm"
include "xaddcl.mm"
include "sylan2.mm"
include "xlt0neg1.mm"
include "syl.mm"
include "cle.mm"
include "wn.mm"
include "xsubge0.mm"
include "notbid.mm"
include "0xr.mm"
include "xrltnle.mm"
include "sylancl.mm"
include "3bitr4d.mm"
include "wceq.mm"
include "xnegdi.mm"
include "xnegneg.mm"
include "oveq2d.mm"
include "adantl.mm"
include "xaddcom.mm"
include "sylan.mm"
include "3eqtrd.mm"
include "breq2d.mm"
include "3bitr3d.mm"

theorem xposdif
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A < B <-> 0 < ( B +e -e A ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    cxne
    #
    cxad
    co
    #
    cc0
    clt
    wbr
    #
    cc0
    @4
    cxne
    #
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    #
    cc0
    cB
    cA
    cxne
    #
    cxad
    co
    #
    clt
    wbr
    @2
    @4
    cxr
    wcel
    #
    @5
    @7
    wb
    @1
    @0
    @3
    cxr
    wcel
    #
    @11
    cB
    xnegcl
    #
    cA
    @3
    xaddcl
    sylan2
    #
    @4
    xlt0neg1
    syl
    @2
    cc0
    @4
    cle
    wbr
    #
    wn
    #
    cB
    cA
    cle
    wbr
    #
    wn
    @5
    @8
    @2
    @15
    @17
    cA
    cB
    xsubge0
    notbid
    @2
    @11
    cc0
    cxr
    wcel
    @5
    @16
    wb
    @14
    0xr
    @4
    cc0
    xrltnle
    sylancl
    cA
    cB
    xrltnle
    3bitr4d
    @2
    @6
    @10
    cc0
    clt
    @2
    @6
    @9
    @3
    cxne
    #
    cxad
    co
    #
    @9
    cB
    cxad
    co
    #
    @10
    @1
    @0
    @12
    @6
    @19
    wceq
    @13
    cA
    @3
    xnegdi
    sylan2
    @1
    @19
    @20
    wceq
    @0
    @1
    @18
    cB
    @9
    cxad
    cB
    xnegneg
    oveq2d
    adantl
    @0
    @9
    cxr
    wcel
    @1
    @20
    @10
    wceq
    cA
    xnegcl
    @9
    cB
    xaddcom
    sylan
    3eqtrd
    breq2d
    3bitr3d
end
