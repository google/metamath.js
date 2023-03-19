include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp2l.mm"
include "simp3r.mm"
include "btwncom.mm"
include "syl13anc.mm"
include "simp2r.mm"
include "anbi12d.mm"
include "wi.mm"
include "axpasch.mm"
include "syl132anc.mm"
include "sylbid.mm"
include "ancomsd.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl3l.mm"
include "axbtwnid.mm"
include "syl3anc.mm"
include "breq1.mm"
include "biimpd.mm"
include "syl6.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syld.mm"

theorem btwnexch3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , C >. /\ C Btwn <. A , D >. ) -> C Btwn <. B , D >. ) )

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
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cC
    cA
    cD
    cop
    cbtwn
    wbr
    #
    wa
    vx
    cv
    #
    cC
    cC
    cop
    cbtwn
    wbr
    #
    @11
    cB
    cD
    cop
    #
    cbtwn
    wbr
    #
    wa
    #
    vx
    @1
    wrex
    #
    cC
    @13
    cbtwn
    wbr
    #
    @8
    @10
    @9
    @16
    @8
    @10
    @9
    wa
    cC
    cD
    cA
    cop
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    cbtwn
    wbr
    #
    wa
    #
    @16
    @8
    @10
    @18
    @9
    @19
    @8
    @0
    @5
    @2
    @6
    @10
    @18
    wb
    @0
    @4
    @7
    simp1
    #
    @0
    @4
    @5
    @6
    simp3l
    #
    @0
    @2
    @3
    @7
    simp2l
    #
    @0
    @4
    @5
    @6
    simp3r
    #
    cC
    cA
    cD
    cN
    btwncom
    syl13anc
    @8
    @0
    @3
    @2
    @5
    @9
    @19
    wb
    @21
    @0
    @2
    @3
    @7
    simp2r
    #
    @23
    @22
    cB
    cA
    cC
    cN
    btwncom
    syl13anc
    anbi12d
    @8
    @0
    @6
    @5
    @2
    @5
    @3
    @20
    @16
    wi
    @21
    @24
    @22
    @23
    @22
    @25
    vx
    cD
    cC
    cA
    cC
    cB
    cN
    axpasch
    syl132anc
    sylbid
    ancomsd
    @8
    @15
    @17
    vx
    @1
    @8
    @11
    @1
    wcel
    #
    wa
    #
    @12
    @14
    @17
    @27
    @12
    @11
    cC
    wceq
    #
    @14
    @17
    wi
    @27
    @0
    @26
    @5
    @12
    @28
    wi
    @0
    @4
    @7
    @26
    simpl1
    @8
    @26
    simpr
    @5
    @6
    @0
    @4
    @26
    simpl3l
    @11
    cC
    cN
    axbtwnid
    syl3anc
    @28
    @14
    @17
    @11
    cC
    @13
    cbtwn
    breq1
    biimpd
    syl6
    impd
    rexlimdva
    syld
end
