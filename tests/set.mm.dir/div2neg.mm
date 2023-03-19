include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cneg.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "negcl.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "div12.mm"
include "syl112anc.mm"
include "c1.mm"
include "divneg.mm"
include "syld3an1.mm"
include "divid.mm"
include "3adant1.mm"
include "negeqd.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "ax-1cn.mm"
include "negcli.mm"
include "mulcom.mm"
include "mpan2.mm"
include "mulm1.mm"
include "eqtrd.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "divcl.mm"
include "negeq0.mm"
include "necon3bid.mm"
include "biimpa.mm"
include "divmul.mm"
include "mpbird.mm"

theorem div2neg
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( -u A / -u B ) = ( A / B ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    #
    cA
    cneg
    #
    cB
    cneg
    #
    cdiv
    co
    cA
    cB
    cdiv
    co
    #
    wceq
    #
    @5
    @6
    cmul
    co
    #
    @4
    wceq
    #
    @3
    @8
    cA
    @5
    cB
    cdiv
    co
    #
    cmul
    co
    #
    @4
    @3
    @5
    cc
    wcel
    #
    @0
    @1
    @2
    @8
    @11
    wceq
    @1
    @0
    @12
    @2
    cB
    negcl
    3ad2ant2
    #
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    @5
    cA
    cB
    div12
    syl112anc
    @3
    @11
    cA
    c1
    cneg
    #
    cmul
    co
    #
    @4
    @3
    @10
    @15
    cA
    cmul
    @3
    cB
    cB
    cdiv
    co
    #
    cneg
    #
    @10
    @15
    @1
    @1
    @0
    @2
    @18
    @10
    wceq
    @14
    cB
    cB
    divneg
    syld3an1
    @3
    @17
    c1
    @1
    @2
    @17
    c1
    wceq
    @0
    cB
    divid
    3adant1
    negeqd
    eqtr3d
    oveq2d
    @0
    @1
    @16
    @4
    wceq
    @2
    @0
    @16
    @15
    cA
    cmul
    co
    #
    @4
    @0
    @15
    cc
    wcel
    @16
    @19
    wceq
    c1
    ax-1cn
    negcli
    cA
    @15
    mulcom
    mpan2
    cA
    mulm1
    eqtrd
    3ad2ant1
    eqtrd
    eqtrd
    @3
    @4
    cc
    wcel
    #
    @6
    cc
    wcel
    @12
    @5
    cc0
    wne
    #
    @7
    @9
    wb
    @0
    @1
    @20
    @2
    cA
    negcl
    3ad2ant1
    cA
    cB
    divcl
    @13
    @1
    @2
    @21
    @0
    @1
    @2
    @21
    @1
    cB
    cc0
    @5
    cc0
    cB
    negeq0
    necon3bid
    biimpa
    3adant1
    @4
    @6
    @5
    divmul
    syl112anc
    mpbird
end
