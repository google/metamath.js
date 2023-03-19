include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "w3a.mm"
include "wa.mm"
include "cint.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "simp1.mm"
include "elpw2g.mm"
include "syl5ibr.mm"
include "imp.mm"
include "simpr3.mm"
include "elind.mm"
include "eqid.mm"
include "inteq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "cvv.mm"
include "wb.mm"
include "simp2.mm"
include "intex.mm"
include "sylib.mm"
include "id.mm"
include "elfi.mm"
include "syl2anr.mm"
include "mpbird.mm"

theorem elfir
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cW: class W


  assert |- ( ( B e. V /\ ( A C_ B /\ A =/= (/) /\ A e. Fin ) ) -> |^| A e. ( fi ` B ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    wss
    #
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cint
    #
    cB
    cfi
    cfv
    wcel
    #
    @6
    vx
    cv
    #
    cint
    #
    wceq
    #
    vx
    cB
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @5
    cA
    @12
    wcel
    @6
    @6
    wceq
    #
    @13
    @5
    @11
    cfn
    cA
    @0
    @4
    cA
    @11
    wcel
    #
    @4
    @15
    @0
    @1
    @1
    @2
    @3
    simp1
    cA
    cB
    cV
    elpw2g
    syl5ibr
    imp
    @0
    @1
    @2
    @3
    simpr3
    elind
    @6
    eqid
    @10
    @14
    vx
    cA
    @12
    @8
    cA
    wceq
    @9
    @6
    @6
    @8
    cA
    inteq
    eqeq2d
    rspcev
    sylancl
    @4
    @6
    cvv
    wcel
    #
    @0
    @7
    @13
    wb
    @0
    @4
    @2
    @16
    @1
    @2
    @3
    simp2
    cA
    intex
    sylib
    @0
    id
    vx
    @6
    cB
    cvv
    cV
    elfi
    syl2anr
    mpbird
end
