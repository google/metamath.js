include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wb.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp2l.mm"
include "simp3l.mm"
include "btwncom.mm"
include "syl13anc.mm"
include "simp3r.mm"
include "anbi12d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "wi.mm"
include "btwnexch2.mm"
include "syl122anc.mm"
include "sylbid.mm"
include "sylibd.mm"

theorem btwnexch
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , C >. /\ C Btwn <. A , D >. ) -> B Btwn <. A , D >. ) )

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
    #
    cbtwn
    wbr
    #
    wa
    #
    cB
    cD
    cA
    cop
    #
    cbtwn
    wbr
    #
    cB
    @10
    cbtwn
    wbr
    #
    @8
    @12
    cC
    @13
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
    @14
    @8
    @12
    @17
    @16
    wa
    @18
    @8
    @9
    @17
    @11
    @16
    @8
    @0
    @3
    @2
    @5
    @9
    @17
    wb
    @0
    @4
    @7
    simp1
    #
    @0
    @2
    @3
    @7
    simp2r
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
    simp3l
    #
    cB
    cA
    cC
    cN
    btwncom
    syl13anc
    @8
    @0
    @5
    @2
    @6
    @11
    @16
    wb
    @19
    @22
    @21
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
    anbi12d
    @17
    @16
    ancom
    syl6bb
    @8
    @0
    @6
    @5
    @3
    @2
    @18
    @14
    wi
    @19
    @23
    @22
    @20
    @21
    cD
    cC
    cB
    cA
    cN
    btwnexch2
    syl122anc
    sylbid
    @8
    @0
    @3
    @6
    @2
    @14
    @15
    wb
    @19
    @20
    @23
    @21
    cB
    cD
    cA
    cN
    btwncom
    syl13anc
    sylibd
end
