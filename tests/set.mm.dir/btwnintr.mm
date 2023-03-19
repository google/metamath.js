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
include "wi.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3r.mm"
include "simp3l.mm"
include "axpasch.mm"
include "syl132anc.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2r.mm"
include "axbtwnid.mm"
include "syl3anc.mm"
include "breq1.mm"
include "biimpa.mm"
include "wb.mm"
include "simpl3l.mm"
include "simpl2l.mm"
include "btwncom.mm"
include "syl13anc.mm"
include "syl5ib.mm"
include "syland.mm"
include "rexlimdva.mm"
include "syld.mm"

theorem btwnintr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , D >. /\ C Btwn <. B , D >. ) -> B Btwn <. A , C >. ) )

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
    cD
    cop
    cbtwn
    wbr
    cC
    cB
    cD
    cop
    cbtwn
    wbr
    wa
    #
    vx
    cv
    #
    cB
    cB
    cop
    cbtwn
    wbr
    #
    @10
    cC
    cA
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
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    @8
    @0
    @2
    @3
    @6
    @3
    @5
    @9
    @15
    wi
    @0
    @4
    @7
    simp1
    @0
    @2
    @3
    @7
    simp2l
    @0
    @2
    @3
    @7
    simp2r
    #
    @0
    @4
    @5
    @6
    simp3r
    @17
    @0
    @4
    @5
    @6
    simp3l
    vx
    cA
    cB
    cD
    cB
    cC
    cN
    axpasch
    syl132anc
    @8
    @14
    @16
    vx
    @1
    @8
    @10
    @1
    wcel
    #
    wa
    #
    @11
    @10
    cB
    wceq
    #
    @13
    @16
    @19
    @0
    @18
    @3
    @11
    @20
    wi
    @0
    @4
    @7
    @18
    simpl1
    #
    @8
    @18
    simpr
    @2
    @3
    @0
    @7
    @18
    simpl2r
    #
    @10
    cB
    cN
    axbtwnid
    syl3anc
    @20
    @13
    wa
    cB
    @12
    cbtwn
    wbr
    #
    @19
    @16
    @20
    @13
    @23
    @10
    cB
    @12
    cbtwn
    breq1
    biimpa
    @19
    @0
    @3
    @5
    @2
    @23
    @16
    wb
    @21
    @22
    @5
    @6
    @0
    @4
    @18
    simpl3l
    @2
    @3
    @0
    @7
    @18
    simpl2l
    cB
    cC
    cA
    cN
    btwncom
    syl13anc
    syl5ib
    syland
    rexlimdva
    syld
end
