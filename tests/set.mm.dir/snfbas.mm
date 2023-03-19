include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cfbas.mm"
include "cfv.mm"
include "cpw.mm"
include "cfil.mm"
include "cvv.mm"
include "ssexg.mm"
include "3adant2.mm"
include "simp2.mm"
include "snfil.mm"
include "syl2anc.mm"
include "filfbas.mm"
include "syl.mm"
include "simp1.mm"
include "wb.mm"
include "elpw2g.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "snssd.mm"
include "simp3.mm"
include "fbasweak.mm"
include "syl3anc.mm"

theorem snfbas
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let cY: class Y


  assert |- ( ( A C_ B /\ A =/= (/) /\ B e. V ) -> { A } e. ( fBas ` B ) )

  proof
    cA
    cB
    wss
    #
    cA
    c0
    wne
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cA
    csn
    #
    cA
    cfbas
    cfv
    wcel
    #
    @4
    cB
    cpw
    #
    wss
    @2
    @4
    cB
    cfbas
    cfv
    wcel
    @3
    @4
    cA
    cfil
    cfv
    wcel
    #
    @5
    @3
    cA
    cvv
    wcel
    #
    @1
    @7
    @0
    @2
    @8
    @1
    cA
    cB
    cV
    ssexg
    3adant2
    @0
    @1
    @2
    simp2
    cA
    cvv
    snfil
    syl2anc
    @4
    cA
    filfbas
    syl
    @3
    cA
    @6
    @3
    cA
    @6
    wcel
    #
    @0
    @0
    @1
    @2
    simp1
    @2
    @0
    @9
    @0
    wb
    @1
    cA
    cB
    cV
    elpw2g
    3ad2ant3
    mpbird
    snssd
    @0
    @1
    @2
    simp3
    @4
    cV
    cA
    cB
    fbasweak
    syl3anc
end
