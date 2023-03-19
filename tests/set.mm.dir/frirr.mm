include "wfr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "csn.mm"
include "crab.mm"
include "c0.mm"
include "wceq.mm"
include "wrex.mm"
include "wn.mm"
include "wss.mm"
include "wne.mm"
include "simpl.mm"
include "snssi.mm"
include "adantl.mm"
include "snnzg.mm"
include "snex.mm"
include "frc.mm"
include "syl3anc.mm"
include "wb.mm"
include "wral.mm"
include "rabeq0.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "rexsng.mm"
include "breq1.mm"
include "ralsng.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem frirr
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R Fr A /\ B e. A ) -> -. B R B )

  proof
    cA
    cR
    wfr
    #
    cB
    cA
    wcel
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    cB
    csn
    #
    crab
    c0
    wceq
    #
    vy
    @6
    wrex
    #
    cB
    cB
    cR
    wbr
    #
    wn
    #
    @2
    @0
    @6
    cA
    wss
    #
    @6
    c0
    wne
    #
    @8
    @0
    @1
    simpl
    @1
    @11
    @0
    cB
    cA
    snssi
    adantl
    @1
    @12
    @0
    cB
    cA
    snnzg
    adantl
    vy
    vx
    cA
    @6
    cR
    cB
    snex
    frc
    syl3anc
    @1
    @8
    @10
    wb
    @0
    @1
    @8
    @3
    cB
    cR
    wbr
    #
    wn
    #
    vx
    @6
    wral
    #
    @10
    @7
    @15
    vy
    cB
    cA
    @7
    @5
    wn
    #
    vx
    @6
    wral
    @4
    cB
    wceq
    #
    @15
    @5
    vx
    @6
    rabeq0
    @17
    @16
    @14
    vx
    @6
    @17
    @5
    @13
    @4
    cB
    @3
    cR
    breq2
    notbid
    ralbidv
    syl5bb
    rexsng
    @14
    @10
    vx
    cB
    cA
    @3
    cB
    wceq
    @13
    @9
    @3
    cB
    cB
    cR
    breq1
    notbid
    ralsng
    bitrd
    adantl
    mpbid
end
