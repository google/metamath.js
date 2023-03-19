include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cpellfund.mm"
include "clt.mm"
include "wa.mm"
include "w3a.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "simp3r.mm"
include "cr.mm"
include "pell14qrre.mm"
include "3adant3.mm"
include "pellfundre.mm"
include "3ad2ant1.mm"
include "ltnled.mm"
include "mpbid.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "pellfundlb.mm"
include "syl3anc.mm"
include "mtand.mm"
include "simp3l.mm"
include "wb.mm"
include "1re.mm"
include "leloe.mm"
include "sylancr.mm"
include "orel1.mm"
include "sylc.mm"
include "eqcomd.mm"

theorem pellfund14gap
  let cA: class A
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ ( 1 <_ A /\ A < ( PellFund ` D ) ) ) -> A = 1 )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    cA
    cD
    cpellfund
    cfv
    #
    clt
    wbr
    #
    wa
    #
    w3a
    #
    c1
    cA
    @6
    c1
    cA
    clt
    wbr
    #
    wn
    @7
    c1
    cA
    wceq
    #
    wo
    #
    @8
    @6
    @7
    @3
    cA
    cle
    wbr
    #
    @6
    @4
    @10
    wn
    @0
    @1
    @2
    @4
    simp3r
    @6
    cA
    @3
    @0
    @1
    cA
    cr
    wcel
    #
    @5
    cA
    cD
    pell14qrre
    3adant3
    #
    @0
    @1
    @3
    cr
    wcel
    @5
    cD
    pellfundre
    3ad2ant1
    ltnled
    mpbid
    @6
    @7
    wa
    @0
    @1
    @7
    @10
    @0
    @1
    @5
    @7
    simpl1
    @0
    @1
    @5
    @7
    simpl2
    @6
    @7
    simpr
    cA
    cD
    pellfundlb
    syl3anc
    mtand
    @6
    @2
    @9
    @0
    @1
    @2
    @4
    simp3l
    @6
    c1
    cr
    wcel
    @11
    @2
    @9
    wb
    1re
    @12
    c1
    cA
    leloe
    sylancr
    mpbid
    @7
    @8
    orel1
    sylc
    eqcomd
end
