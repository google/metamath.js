include "wcel.mm"
include "w3a.mm"
include "cin.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cint.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "wrex.mm"
include "cpr.mm"
include "prelpwi.mm"
include "3adant1.mm"
include "prfi.mm"
include "a1i.mm"
include "elind.mm"
include "intprg.mm"
include "eqcomd.mm"
include "inteq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wb.mm"
include "inex1g.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "elfi.mm"
include "mpbird.mm"

theorem inelfi
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let vp: setvar p


  assert |- ( ( X e. V /\ A e. X /\ B e. X ) -> ( A i^i B ) e. ( fi ` X ) )

  proof
    cX
    cV
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
    cin
    #
    cX
    cfi
    cfv
    wcel
    #
    @4
    vp
    cv
    #
    cint
    #
    wceq
    #
    vp
    cX
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @3
    cA
    cB
    cpr
    #
    @10
    wcel
    @4
    @12
    cint
    #
    wceq
    #
    @11
    @3
    @9
    cfn
    @12
    @1
    @2
    @12
    @9
    wcel
    @0
    cA
    cB
    cX
    prelpwi
    3adant1
    @12
    cfn
    wcel
    @3
    cA
    cB
    prfi
    a1i
    elind
    @3
    @13
    @4
    @1
    @2
    @13
    @4
    wceq
    @0
    cA
    cB
    cX
    cX
    intprg
    3adant1
    eqcomd
    @8
    @14
    vp
    @12
    @10
    @6
    @12
    wceq
    @7
    @13
    @4
    @6
    @12
    inteq
    eqeq2d
    rspcev
    syl2anc
    @3
    @4
    cvv
    wcel
    #
    @0
    @5
    @11
    wb
    @1
    @0
    @15
    @2
    cA
    cB
    cX
    inex1g
    3ad2ant2
    @0
    @1
    @2
    simp1
    vp
    @4
    cX
    cvv
    cV
    elfi
    syl2anc
    mpbird
end
