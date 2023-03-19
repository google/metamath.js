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
include "simpl2.mm"
include "simpr.mm"
include "simpl3.mm"
include "axcgrid.mm"
include "syl13anc.mm"
include "opeq2.mm"
include "breq1d.mm"
include "biimprd.mm"
include "syli.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem cgrtriv
  let cA: class A
  let cB: class B
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) -> <. A , A >. Cgr <. B , B >. )

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
    cA
    cA
    vx
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @6
    cB
    cB
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    #
    cA
    cA
    cop
    #
    @8
    ccgr
    wbr
    #
    @4
    @0
    @2
    @2
    @3
    @3
    @11
    @0
    @2
    @3
    simp1
    @0
    @2
    @3
    simp2
    #
    @14
    @0
    @2
    @3
    simp3
    #
    @15
    vx
    cA
    cA
    cB
    cB
    cN
    axsegcon
    syl122anc
    @4
    @10
    @13
    vx
    @1
    @4
    @5
    @1
    wcel
    #
    wa
    #
    @9
    @13
    @7
    @9
    @17
    cA
    @5
    wceq
    #
    @13
    @17
    @0
    @2
    @16
    @3
    @9
    @18
    wi
    @0
    @2
    @3
    @16
    simpl1
    @0
    @2
    @3
    @16
    simpl2
    @4
    @16
    simpr
    @0
    @2
    @3
    @16
    simpl3
    cA
    @5
    cB
    cN
    axcgrid
    syl13anc
    @18
    @13
    @9
    @18
    @12
    @6
    @8
    ccgr
    cA
    @5
    cA
    opeq2
    breq1d
    biimprd
    syli
    adantld
    rexlimdva
    mpd
end
