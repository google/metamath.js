include "cxr.mm"
include "wcel.mm"
include "w3a.mm"
include "cico.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "elin.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wb.mm"
include "elico1.mm"
include "3adant3.mm"
include "biimpa.mm"
include "simp3d.mm"
include "adantrr.mm"
include "wn.mm"
include "3adant1.mm"
include "simp2d.mm"
include "simpl2.mm"
include "simp1d.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "adantrl.mm"
include "pm2.65da.mm"
include "pm2.21d.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ss0.mm"
include "syl.mm"

theorem icodisj
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( ( A [,) B ) i^i ( B [,) C ) ) = (/) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    w3a
    #
    cA
    cB
    cico
    co
    #
    cB
    cC
    cico
    co
    #
    cin
    #
    c0
    wss
    @6
    c0
    wceq
    @3
    vx
    @6
    c0
    vx
    cv
    #
    @6
    wcel
    @7
    @4
    wcel
    #
    @7
    @5
    wcel
    #
    wa
    #
    @3
    @7
    c0
    wcel
    #
    @7
    @4
    @5
    elin
    @3
    @10
    @11
    @3
    @10
    @7
    cB
    clt
    wbr
    #
    @3
    @8
    @12
    @9
    @3
    @8
    wa
    @7
    cxr
    wcel
    #
    cA
    @7
    cle
    wbr
    #
    @12
    @3
    @8
    @13
    @14
    @12
    w3a
    #
    @0
    @1
    @8
    @15
    wb
    @2
    cA
    cB
    @7
    elico1
    3adant3
    biimpa
    simp3d
    adantrr
    @3
    @9
    @12
    wn
    #
    @8
    @3
    @9
    wa
    #
    cB
    @7
    cle
    wbr
    #
    @16
    @17
    @13
    @18
    @7
    cC
    clt
    wbr
    #
    @3
    @9
    @13
    @18
    @19
    w3a
    #
    @1
    @2
    @9
    @20
    wb
    @0
    cB
    cC
    @7
    elico1
    3adant1
    biimpa
    #
    simp2d
    @17
    @1
    @13
    @18
    @16
    wb
    @0
    @1
    @2
    @9
    simpl2
    @17
    @13
    @18
    @19
    @21
    simp1d
    cB
    @7
    xrlenlt
    syl2anc
    mpbid
    adantrl
    pm2.65da
    pm2.21d
    syl5bi
    ssrdv
    @6
    ss0
    syl
end
