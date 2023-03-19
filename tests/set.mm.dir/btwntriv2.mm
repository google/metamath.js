include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wa.mm"
include "wrex.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "axsegcon.mm"
include "syl122anc.mm"
include "wceq.mm"
include "wi.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simpr.mm"
include "axcgrid.mm"
include "syl13anc.mm"
include "opeq2.mm"
include "breq2d.mm"
include "biimprd.mm"
include "syl6.mm"
include "impd.mm"
include "ancomsd.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem btwntriv2
  let cA: class A
  let cB: class B
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> B Btwn <. A , B >. )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cB
    cA
    vx
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    cB
    @5
    cop
    cB
    cB
    cop
    ccgr
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    #
    cB
    cA
    cB
    cop
    #
    cbtwn
    wbr
    #
    @4
    @0
    @2
    @3
    @3
    @3
    @10
    @0
    @2
    @3
    simp1
    @0
    @2
    @3
    simp2
    @0
    @2
    @3
    simp3
    #
    @13
    @13
    vx
    cA
    cB
    cB
    cB
    cN
    axsegcon
    syl122anc
    @4
    @9
    @12
    vx
    @1
    @4
    @5
    @1
    wcel
    #
    wa
    #
    @8
    @7
    @12
    @15
    @8
    @7
    @12
    @15
    @8
    cB
    @5
    wceq
    #
    @7
    @12
    wi
    @15
    @0
    @3
    @14
    @3
    @8
    @16
    wi
    @0
    @2
    @3
    @14
    simpl1
    @0
    @2
    @3
    @14
    simpl3
    #
    @4
    @14
    simpr
    @17
    cB
    @5
    cB
    cN
    axcgrid
    syl13anc
    @16
    @12
    @7
    @16
    @11
    @6
    cB
    cbtwn
    cB
    @5
    cA
    opeq2
    breq2d
    biimprd
    syl6
    impd
    ancomsd
    rexlimdva
    mpd
end
