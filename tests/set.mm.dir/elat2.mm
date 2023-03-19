include "cat.mm"
include "wcel.mm"
include "cch.mm"
include "c0h.mm"
include "ccv.mm"
include "wbr.mm"
include "wa.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "ela.mm"
include "wpss.mm"
include "wb.mm"
include "h0elch.mm"
include "cvbr2.mm"
include "mpan.mm"
include "ch0pss.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "impexp.mm"
include "bi2.04.mm"
include "bitri.mm"
include "orcom.mm"
include "neor.mm"
include "imbi2i.mm"
include "3bitr4g.mm"
include "ralbiia.mm"
include "a1i.mm"
include "anbi12d.mm"
include "bitr2d.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem elat2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A e. HAtoms <-> ( A e. CH /\ ( A =/= 0H /\ A. x e. CH ( x C_ A -> ( x = A \/ x = 0H ) ) ) ) )

  proof
    cA
    cat
    wcel
    cA
    cch
    wcel
    #
    c0h
    cA
    ccv
    wbr
    #
    wa
    @0
    cA
    c0h
    wne
    #
    vx
    cv
    #
    cA
    wss
    #
    @3
    cA
    wceq
    #
    @3
    c0h
    wceq
    #
    wo
    #
    wi
    #
    vx
    cch
    wral
    #
    wa
    #
    wa
    cA
    ela
    @0
    @10
    @1
    @0
    @1
    c0h
    cA
    wpss
    #
    c0h
    @3
    wpss
    #
    @4
    wa
    @5
    wi
    #
    vx
    cch
    wral
    #
    wa
    #
    @10
    c0h
    cch
    wcel
    @0
    @1
    @15
    wb
    h0elch
    vx
    c0h
    cA
    cvbr2
    mpan
    @0
    @11
    @2
    @14
    @9
    cA
    ch0pss
    @14
    @9
    wb
    @0
    @13
    @8
    vx
    cch
    @3
    cch
    wcel
    #
    @4
    @12
    @5
    wi
    #
    wi
    #
    @4
    @3
    c0h
    wne
    #
    @5
    wi
    #
    wi
    @13
    @8
    @16
    @17
    @20
    @4
    @16
    @12
    @19
    @5
    @3
    ch0pss
    imbi1d
    imbi2d
    @13
    @12
    @4
    @5
    wi
    wi
    @18
    @12
    @4
    @5
    impexp
    @12
    @4
    @5
    bi2.04
    bitri
    @7
    @20
    @4
    @7
    @6
    @5
    wo
    @20
    @5
    @6
    orcom
    @5
    @3
    c0h
    neor
    bitri
    imbi2i
    3bitr4g
    ralbiia
    a1i
    anbi12d
    bitr2d
    pm5.32i
    bitr4i
end
