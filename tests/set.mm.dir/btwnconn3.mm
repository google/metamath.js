include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wne.mm"
include "wrex.mm"
include "wo.mm"
include "wi.mm"
include "simp1.mm"
include "simp3r.mm"
include "simp2l.mm"
include "btwndiff.mm"
include "syl3anc.mm"
include "simprlr.mm"
include "necomd.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpr.mm"
include "simpl3r.mm"
include "simprrl.mm"
include "btwncomand.mm"
include "simprll.mm"
include "btwnexch3and.mm"
include "simpl3l.mm"
include "simprrr.mm"
include "3jca.mm"
include "ex.mm"
include "btwnconn2.mm"
include "syl122anc.mm"
include "syld.mm"
include "expd.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem btwnconn3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vp: setvar p


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , D >. /\ C Btwn <. A , D >. ) -> ( B Btwn <. A , C >. \/ C Btwn <. A , B >. ) ) )

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
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cD
    vp
    cv
    #
    cop
    cbtwn
    wbr
    #
    cA
    @9
    wne
    #
    wa
    #
    vp
    @1
    wrex
    #
    cB
    cA
    cD
    cop
    #
    cbtwn
    wbr
    #
    cC
    @14
    cbtwn
    wbr
    #
    wa
    #
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    cC
    cA
    cB
    cop
    cbtwn
    wbr
    wo
    #
    wi
    #
    @8
    @0
    @6
    @2
    @13
    @0
    @4
    @7
    simp1
    @0
    @4
    @5
    @6
    simp3r
    @0
    @2
    @3
    @7
    simp2l
    cD
    cA
    cN
    vp
    btwndiff
    syl3anc
    @8
    @12
    @19
    vp
    @1
    @8
    @9
    @1
    wcel
    #
    wa
    #
    @12
    @17
    @18
    @21
    @12
    @17
    wa
    #
    @9
    cA
    wne
    #
    cA
    @9
    cB
    cop
    cbtwn
    wbr
    #
    cA
    @9
    cC
    cop
    cbtwn
    wbr
    #
    w3a
    #
    @18
    @21
    @22
    @26
    @21
    @22
    wa
    #
    @23
    @24
    @25
    @27
    cA
    @9
    @21
    @10
    @11
    @17
    simprlr
    necomd
    @21
    @22
    cA
    cB
    @9
    cN
    @0
    @4
    @7
    @20
    simpl1
    #
    @2
    @3
    @0
    @7
    @20
    simpl2l
    #
    @2
    @3
    @0
    @7
    @20
    simpl2r
    #
    @8
    @20
    simpr
    #
    @21
    @22
    cD
    cB
    cA
    @9
    cN
    @28
    @5
    @6
    @0
    @4
    @20
    simpl3r
    #
    @30
    @29
    @31
    @21
    @22
    cB
    cA
    cD
    cN
    @28
    @30
    @29
    @32
    @21
    @12
    @15
    @16
    simprrl
    btwncomand
    @21
    @10
    @11
    @17
    simprll
    #
    btwnexch3and
    btwncomand
    @21
    @22
    cA
    cC
    @9
    cN
    @28
    @29
    @5
    @6
    @0
    @4
    @20
    simpl3l
    #
    @31
    @21
    @22
    cD
    cC
    cA
    @9
    cN
    @28
    @32
    @34
    @29
    @31
    @21
    @22
    cC
    cA
    cD
    cN
    @28
    @34
    @29
    @32
    @21
    @12
    @15
    @16
    simprrr
    btwncomand
    @33
    btwnexch3and
    btwncomand
    3jca
    ex
    @21
    @0
    @20
    @2
    @3
    @5
    @26
    @18
    wi
    @28
    @31
    @29
    @30
    @34
    @9
    cA
    cB
    cC
    cN
    btwnconn2
    syl122anc
    syld
    expd
    rexlimdva
    mpd
end
