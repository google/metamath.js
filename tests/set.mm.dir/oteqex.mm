include "cop.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wi.mm"
include "simp3.mm"
include "a1i.mm"
include "oteqex2.mm"
include "syl5ibr.mm"
include "wb.mm"
include "wa.mm"
include "opex.mm"
include "opthg.mm"
include "mpan.mm"
include "simprbda.mm"
include "opeqex.mm"
include "syl.mm"
include "adantl.mm"
include "anbi12d.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "expcom.mm"
include "pm5.21ndd.mm"

theorem oteqex
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T


  assert |- ( <. <. A , B >. , C >. = <. <. R , S >. , T >. -> ( ( A e. _V /\ B e. _V /\ C e. _V ) <-> ( R e. _V /\ S e. _V /\ T e. _V ) ) )

  proof
    cA
    cB
    cop
    #
    cC
    cop
    cR
    cS
    cop
    #
    cT
    cop
    wceq
    #
    cC
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @3
    w3a
    #
    cR
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    cT
    cvv
    wcel
    #
    w3a
    #
    @6
    @3
    wi
    @2
    @4
    @5
    @3
    simp3
    a1i
    @10
    @3
    @2
    @9
    @7
    @8
    @9
    simp3
    cA
    cB
    cC
    cR
    cS
    cT
    oteqex2
    #
    syl5ibr
    @3
    @2
    @6
    @10
    wb
    @3
    @2
    wa
    #
    @4
    @5
    wa
    #
    @3
    wa
    @7
    @8
    wa
    #
    @9
    wa
    @6
    @10
    @12
    @13
    @14
    @3
    @9
    @12
    @0
    @1
    wceq
    #
    @13
    @14
    wb
    @3
    @2
    @15
    cC
    cT
    wceq
    #
    @0
    cvv
    wcel
    @3
    @2
    @15
    @16
    wa
    wb
    cA
    cB
    opex
    @0
    cC
    @1
    cT
    cvv
    cvv
    opthg
    mpan
    simprbda
    cA
    cB
    cR
    cS
    opeqex
    syl
    @2
    @3
    @9
    wb
    @3
    @11
    adantl
    anbi12d
    @4
    @5
    @3
    df-3an
    @7
    @8
    @9
    df-3an
    3bitr4g
    expcom
    pm5.21ndd
end
