include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "cima.mm"
include "cuni.mm"
include "cdm.mm"
include "wlim.mm"
include "word.mm"
include "wss.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ordsson.mm"
include "mp2b.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "cpw.mm"
include "wtr.mm"
include "wi.mm"
include "r1tr.mm"
include "trss.mm"
include "ax-mp.mm"
include "elpwg.mm"
include "mpbird.mm"
include "wceq.mm"
include "r1sucg.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "suceq.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rankwflemb.mm"
include "sylibr.mm"

theorem r1elwf
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A e. ( R1 ` B ) -> A e. U. ( R1 " On ) )

  proof
    cA
    cB
    cr1
    cfv
    #
    wcel
    #
    cA
    vx
    cv
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    vx
    con0
    wrex
    #
    cA
    cr1
    con0
    cima
    cuni
    wcel
    @1
    cB
    con0
    wcel
    cA
    cB
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    @6
    @1
    cr1
    cdm
    #
    con0
    cB
    @10
    wlim
    #
    @10
    word
    @10
    con0
    wss
    cr1
    wfun
    @11
    r1funlim
    simpri
    @10
    limord
    @10
    ordsson
    mp2b
    cA
    cB
    cr1
    elfvdm
    #
    sseldi
    @1
    cA
    @0
    cpw
    #
    @8
    @1
    cA
    @13
    wcel
    cA
    @0
    wss
    #
    @0
    wtr
    @1
    @14
    wi
    cB
    r1tr
    @0
    cA
    trss
    ax-mp
    cA
    @0
    @0
    elpwg
    mpbird
    @1
    cB
    @10
    wcel
    @8
    @13
    wceq
    @12
    cB
    r1sucg
    syl
    eleqtrrd
    @5
    @9
    vx
    cB
    con0
    @2
    cB
    wceq
    #
    @4
    @8
    cA
    @15
    @3
    @7
    cr1
    @2
    cB
    suceq
    fveq2d
    eleq2d
    rspcev
    syl2anc
    vx
    cA
    rankwflemb
    sylibr
end
