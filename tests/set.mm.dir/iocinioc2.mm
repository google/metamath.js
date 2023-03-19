include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cioc.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "clt.mm"
include "elin.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl3.mm"
include "elioc1.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "anbi12d.mm"
include "simp31.mm"
include "3adant3.mm"
include "simp2.mm"
include "simp32.mm"
include "xrlelttrd.mm"
include "simp33.mm"
include "3jca.mm"
include "3expia.mm"
include "pm4.71rd.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem iocinioc2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ A <_ B ) -> ( ( A (,] C ) i^i ( B (,] C ) ) = ( B (,] C ) )

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
    cle
    wbr
    #
    wa
    #
    vx
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
    @7
    @5
    vx
    cv
    #
    @8
    wcel
    #
    @9
    cxr
    wcel
    #
    cB
    @9
    clt
    wbr
    #
    @9
    cC
    cle
    wbr
    #
    w3a
    #
    @9
    @7
    wcel
    #
    @10
    @9
    @6
    wcel
    #
    @15
    wa
    #
    @5
    @14
    @9
    @6
    @7
    elin
    @5
    @17
    @11
    cA
    @9
    clt
    wbr
    #
    @13
    w3a
    #
    @14
    wa
    @14
    @5
    @16
    @19
    @15
    @14
    @5
    @0
    @2
    @16
    @19
    wb
    @0
    @1
    @2
    @4
    simpl1
    #
    @0
    @1
    @2
    @4
    simpl3
    #
    cA
    cC
    @9
    elioc1
    syl2anc
    @5
    @1
    @2
    @15
    @14
    wb
    @0
    @1
    @2
    @4
    simpl2
    #
    @21
    cB
    cC
    @9
    elioc1
    syl2anc
    #
    anbi12d
    @5
    @14
    @19
    @3
    @4
    @14
    @19
    @3
    @4
    @14
    w3a
    #
    @11
    @18
    @13
    @3
    @4
    @11
    @12
    @13
    simp31
    #
    @24
    cA
    cB
    @9
    @3
    @4
    @0
    @14
    @20
    3adant3
    @3
    @4
    @1
    @14
    @22
    3adant3
    @25
    @3
    @4
    @14
    simp2
    @3
    @4
    @11
    @12
    @13
    simp32
    xrlelttrd
    @3
    @4
    @11
    @12
    @13
    simp33
    3jca
    3expia
    pm4.71rd
    bitr4d
    syl5bb
    @23
    bitr4d
    eqrdv
end
