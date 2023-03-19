include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "wral.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "cqs.mm"
include "wn.mm"
include "ecdmn0.mm"
include "ralbii.mm"
include "dfss3.mm"
include "wrex.mm"
include "wceq.mm"
include "nne.mm"
include "rexbii.mm"
include "notbii.mm"
include "dfral2.mm"
include "0ex.mm"
include "elqs.mm"
include "eqcom.mm"
include "bitri.mm"
include "3bitr4ri.mm"

theorem n0elqs
  let cA: class A
  let cR: class R
  let vx: setvar x


  assert |- ( -. (/) e. ( A /. R ) <-> A C_ dom R )

  proof
    vx
    cv
    #
    cR
    cdm
    #
    wcel
    #
    vx
    cA
    wral
    @0
    cR
    cec
    #
    c0
    wne
    #
    vx
    cA
    wral
    #
    cA
    @1
    wss
    c0
    cA
    cR
    cqs
    wcel
    #
    wn
    #
    @2
    @4
    vx
    cA
    @0
    cR
    ecdmn0
    ralbii
    vx
    cA
    @1
    dfss3
    @4
    wn
    #
    vx
    cA
    wrex
    #
    wn
    @3
    c0
    wceq
    #
    vx
    cA
    wrex
    #
    wn
    @5
    @7
    @9
    @11
    @8
    @10
    vx
    cA
    @3
    c0
    nne
    rexbii
    notbii
    @4
    vx
    cA
    dfral2
    @6
    @11
    @6
    c0
    @3
    wceq
    #
    vx
    cA
    wrex
    @11
    vx
    cA
    c0
    cR
    0ex
    elqs
    @12
    @10
    vx
    cA
    c0
    @3
    eqcom
    rexbii
    bitri
    notbii
    3bitr4ri
    3bitr4ri
end
