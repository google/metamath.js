include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp3r.mm"
include "simp2l.mm"
include "wb.mm"
include "necom.mm"
include "a1i.mm"
include "simp3l.mm"
include "btwncom.mm"
include "syl13anc.mm"
include "3anbi123d.mm"
include "3ancomb.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "wi.mm"
include "btwnouttr2.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mpd.mm"
include "btwncomand.mm"
include "ex.mm"

theorem btwnouttr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( B =/= C /\ B Btwn <. A , C >. /\ C Btwn <. B , D >. ) -> B Btwn <. A , D >. ) )

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
    cC
    wne
    #
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cC
    cB
    cD
    cop
    cbtwn
    wbr
    #
    w3a
    #
    cB
    cA
    cD
    cop
    cbtwn
    wbr
    @8
    @12
    cB
    cD
    cA
    cN
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
    @4
    @5
    @6
    simp3r
    #
    @0
    @2
    @3
    @7
    simp2l
    #
    @8
    @12
    wa
    cC
    cB
    wne
    #
    cC
    cD
    cB
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
    w3a
    #
    cB
    cD
    cA
    cop
    cbtwn
    wbr
    #
    @8
    @12
    @20
    @8
    @12
    @17
    @19
    @18
    w3a
    @20
    @8
    @9
    @17
    @10
    @19
    @11
    @18
    @9
    @17
    wb
    @8
    cB
    cC
    necom
    a1i
    @8
    @0
    @3
    @2
    @5
    @10
    @19
    wb
    @13
    @14
    @16
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
    @3
    @6
    @11
    @18
    wb
    @13
    @22
    @14
    @15
    cC
    cB
    cD
    cN
    btwncom
    syl13anc
    3anbi123d
    @17
    @19
    @18
    3ancomb
    syl6bb
    biimpa
    @8
    @20
    @21
    wi
    #
    @12
    @8
    @0
    @6
    @5
    @3
    @2
    @23
    @13
    @15
    @22
    @14
    @16
    cD
    cC
    cB
    cA
    cN
    btwnouttr2
    syl122anc
    adantr
    mpd
    btwncomand
    ex
end
