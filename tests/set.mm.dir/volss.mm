include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "covol.mm"
include "cfv.mm"
include "cle.mm"
include "cr.mm"
include "wbr.mm"
include "simp3.mm"
include "mblss.mm"
include "3ad2ant2.mm"
include "ovolss.mm"
include "syl2anc.mm"
include "wceq.mm"
include "mblvol.mm"
include "3ad2ant1.mm"
include "3brtr4d.mm"

theorem volss
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom vol /\ B e. dom vol /\ A C_ B ) -> ( vol ` A ) <_ ( vol ` B ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    wss
    #
    w3a
    #
    cA
    covol
    cfv
    #
    cB
    covol
    cfv
    #
    cA
    cvol
    cfv
    #
    cB
    cvol
    cfv
    #
    cle
    @4
    @3
    cB
    cr
    wss
    #
    @5
    @6
    cle
    wbr
    @1
    @2
    @3
    simp3
    @2
    @1
    @9
    @3
    cB
    mblss
    3ad2ant2
    cA
    cB
    ovolss
    syl2anc
    @1
    @2
    @7
    @5
    wceq
    @3
    cA
    mblvol
    3ad2ant1
    @2
    @1
    @8
    @6
    wceq
    @3
    cB
    mblvol
    3ad2ant2
    3brtr4d
end
