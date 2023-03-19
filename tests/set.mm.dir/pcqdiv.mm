include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cpc.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "caddc.mm"
include "cmul.mm"
include "cc.mm"
include "simp2l.mm"
include "qcn.mm"
include "syl.mm"
include "simp3l.mm"
include "simp3r.mm"
include "divcan1d.mm"
include "oveq2d.mm"
include "wceq.mm"
include "simp1.mm"
include "qdivcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "divne0d.mm"
include "pcqmul.mm"
include "syl122anc.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "cz.mm"
include "pcqcl.mm"
include "syl12anc.mm"
include "zcnd.mm"
include "3adant2.mm"
include "pncand.mm"
include "eqtr2d.mm"

theorem pcqdiv
  let cA: class A
  let cB: class B
  let cP: class P
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let vp: setvar p
  let vr: setvar r
  let vz: setvar z
  let cN: class N


  assert |- ( ( P e. Prime /\ ( A e. QQ /\ A =/= 0 ) /\ ( B e. QQ /\ B =/= 0 ) ) -> ( P pCnt ( A / B ) ) = ( ( P pCnt A ) - ( P pCnt B ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cq
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cq
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    w3a
    #
    cP
    cA
    cpc
    co
    #
    cP
    cB
    cpc
    co
    #
    cmin
    co
    cP
    cA
    cB
    cdiv
    co
    #
    cpc
    co
    #
    @9
    caddc
    co
    #
    @9
    cmin
    co
    @11
    @7
    @8
    @12
    @9
    cmin
    @7
    cP
    @10
    cB
    cmul
    co
    #
    cpc
    co
    #
    @8
    @12
    @7
    @13
    cA
    cP
    cpc
    @7
    cA
    cB
    @7
    @1
    cA
    cc
    wcel
    @0
    @1
    @2
    @6
    simp2l
    #
    cA
    qcn
    syl
    #
    @7
    @4
    cB
    cc
    wcel
    @0
    @3
    @4
    @5
    simp3l
    #
    cB
    qcn
    syl
    #
    @0
    @3
    @4
    @5
    simp3r
    #
    divcan1d
    oveq2d
    @7
    @0
    @10
    cq
    wcel
    #
    @10
    cc0
    wne
    #
    @4
    @5
    @14
    @12
    wceq
    @0
    @3
    @6
    simp1
    #
    @7
    @1
    @4
    @5
    @20
    @15
    @17
    @19
    cA
    cB
    qdivcl
    syl3anc
    #
    @7
    cA
    cB
    @16
    @18
    @0
    @1
    @2
    @6
    simp2r
    @19
    divne0d
    #
    @17
    @19
    @10
    cB
    cP
    pcqmul
    syl122anc
    eqtr3d
    oveq1d
    @7
    @11
    @9
    @7
    @11
    @7
    @0
    @20
    @21
    @11
    cz
    wcel
    @22
    @23
    @24
    cP
    @10
    pcqcl
    syl12anc
    zcnd
    @7
    @9
    @0
    @6
    @9
    cz
    wcel
    @3
    cP
    cB
    pcqcl
    3adant2
    zcnd
    pncand
    eqtr2d
end
